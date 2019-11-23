theory a3
imports
  "AutoCorres.AutoCorres"
  "AutoCorres.TypHeapSimple"
begin

(* To run this file you need the AutoCorres tool used
   in the lecture.

  1. Download AutoCorres from 
       \url{http://www.cse.unsw.edu.au/~cs4161/autocorres-1.6.1.tar}

  2. Unpack the .tar.gz file, which will create the directory autocorres-1.6.1
       tar -xzf autocorres-1.6.1.tar.gz

  3. Build the AutoCorres heap
     L4V_ARCH=X64 isabelle build -v -b -d autocorres-1.6.1 AutoCorres

  4. Load this file using the AutoCorres heap
     L4V_ARCH=X64 isabelle jedit -d autocorres-1.6.1 -l AutoCorres a3.thy

*)

section "Question: Reverse "

(* Hints: 
    - use find_theorems to find Isabelle library theorems about existing concepts.
    - you are allowed to use sledgehammer and other automation
    - if you can't prove one of the lemmas below, you can still assume it in the rest of the proof
    - the function @{const int} converts an Isabelle nat to an int
    - the function @{const nat} converts an Isabelle int to a nat
    - If you want to use apply style, you could the tactic @{text insert assms} 
      to insert assumptions into your proof.
*)

(* Parse the input file. *)
install_C_file "reverse.c"

(* Abstract the input file. *)
autocorres[unsigned_word_abs=reverse] "reverse.c"


section \<open>utility lemmas\<close>

(* This makes an intro rule which can be used with rule_tac, as opposed to
    using whileLoop_add_inv and subst. *)
lemma whileLoop_add_invI:
  assumes "\<lbrace> P \<rbrace> whileLoop_inv c b init I (measure M) \<lbrace> Q \<rbrace>!"
  shows "\<lbrace> P \<rbrace> whileLoop c b init \<lbrace> Q \<rbrace>!"
  by (metis assms whileLoop_inv_def)

lemma pointer_add_ldistrib_add:
  "p +\<^sub>p (a + b) = (p +\<^sub>p a) +\<^sub>p b"
  unfolding ptr_add_def
  by (simp add: algebra_simps)

lemma heap_w32_update_comp: 
  "heap_w32_update (f \<circ> g) s = heap_w32_update f (heap_w32_update g s)"
  by simp

text \<open> This assumes that pointers are wellbehaved \<close>
definition wellbehaved_pointers :: "('a :: c_type) ptr \<Rightarrow> nat \<Rightarrow> bool" where
  "wellbehaved_pointers p n \<equiv> 
    \<forall>i j :: int. i < n \<longrightarrow> j < n \<longrightarrow> ((p +\<^sub>p i :: 'a ptr) = p +\<^sub>p j) \<longleftrightarrow> (i = j)"

lemma wellbehaved_pointers_D:
  fixes n :: nat
  and i j :: int
  assumes
    "wellbehaved_pointers p n"
    "i < n"
    "j < n"
  shows
    "(p +\<^sub>p i = p +\<^sub>p j) \<longleftrightarrow> (i = j)"
  using assms
  by (simp add: wellbehaved_pointers_def)

lemma int_geq_0_less_Suc_eq_0_disj:
  fixes a b :: int
  assumes
    "0 \<le> a"
    "0 \<le> b"
  shows
    "a < 1 + b \<longleftrightarrow> a = 0 \<or> (\<exists>a'. a = 1 + a' \<and> 0 \<le> a' \<and> a' < b)"
  using assms
  by presburger

lemma geq_step_Suc:
  "(\<forall>x\<ge>m. P x) = (P m \<and> (\<forall>x\<ge>Suc m. P x))"
  by (metis Suc_leD dual_order.antisym not_less_eq_eq)

lemma gr_is_geq_Suc:
  "(\<forall>x>m. P x) = ((\<forall>x\<ge>Suc m. P x))"
  by (simp add: Suc_le_eq)

lemma leq_minus_split:
    "i \<le> n - m \<longleftrightarrow> i \<le> n - Suc m \<or> i = n - m"
  by linarith

lemma gr_minus_Suc:
  assumes
    "m > n"
  shows
    "(\<forall>x>m - Suc n. P x) \<longleftrightarrow> P (m - n) \<and> (\<forall>x>m - n. P x)"
  using assms
  apply (simp add: gr_is_geq_Suc Suc_diff_Suc)
  apply (subst (1) le_less)
  apply (simp add: Suc_le_eq split_all_conj)
  apply fast
  done


(*******************************************************************************)

primrec
  arr_is_valid :: "lifted_globals \<Rightarrow> word32 ptr \<Rightarrow> nat \<Rightarrow> bool"
where
    "arr_is_valid s p 0 = True"
  | "arr_is_valid s p (Suc n) = (is_valid_w32 s p \<and> arr_is_valid s (p +\<^sub>p 1) n)"


lemma arr_is_valid_update_heap:
  "arr_is_valid (heap_w32_update f s) p n \<longleftrightarrow> arr_is_valid s p n"
  by (induct n arbitrary: p) simp+

lemma arr_is_valid_conv_all_nth:
  "arr_is_valid s p n \<longleftrightarrow> (\<forall>i<n. is_valid_w32 s (p +\<^sub>p int i))"
  by (induct n arbitrary: p)                 
    (simp add: All_less_Suc2 pointer_add_ldistrib_add)+

lemma arr_is_validD:
  "arr_is_valid s p n \<Longrightarrow> i < n \<Longrightarrow> is_valid_w32 s (p +\<^sub>p int i)"
  using arr_is_valid_conv_all_nth
  by blast

lemma arr_is_valid_intD:
  "arr_is_valid s p n \<Longrightarrow> 0 \<le> i \<Longrightarrow> nat i < n \<Longrightarrow> is_valid_w32 s (p +\<^sub>p i)"
  using arr_is_valid_conv_all_nth
  by auto

lemma arr_is_valid_smaller:
  "arr_is_valid s p n \<Longrightarrow> m \<le> n \<Longrightarrow> arr_is_valid s p m"
  by (simp add: arr_is_valid_conv_all_nth)


subsection \<open> arr_is_valid \<close>

primrec
  arr_list :: "lifted_globals \<Rightarrow> word32 ptr \<Rightarrow> nat \<Rightarrow> word32 list"
where
    "arr_list s p 0 = []"
  | "arr_list s p (Suc n) = (heap_w32 s p) # arr_list s (p +\<^sub>p 1) n"


lemma heap_to_arr_list_lookup:
  fixes i :: int
  assumes
    "0 \<le> i"
    "i < n"
  shows "heap_w32 s (p +\<^sub>p i) = arr_list s p n ! nat i"
  using assms
  apply (induct n arbitrary: p i)
   apply simp
  apply (clarsimp simp add: nth_Cons int_geq_0_less_Suc_eq_0_disj split: nat.splits)
  apply (force simp add: pointer_add_ldistrib_add dest: Suc_nat_eq_nat_zadd1)
  done

lemma arr_list_to_heap_lookup:
  assumes "i < n"
  shows "arr_list s p n ! i = heap_w32 s (p +\<^sub>p int i)"
  using assms
  by (induct n arbitrary: p i) (force simp: less_Suc_eq_0_disj pointer_add_ldistrib_add)+


lemma arr_list_length: "length (arr_list s p n) = n"
  by (induct n arbitrary: p) force+

lemma arr_list_empty_iff: "arr_list s p n = [] \<longleftrightarrow> n = 0"
  by (metis arr_list.simps(1) arr_list_length)

lemma arr_list_heap_update:
  assumes
    "wellbehaved_pointers p n"
    "0 \<le> i"
    "nat i < n"
    "arr_is_valid s p n"
  shows
    "arr_list (heap_w32_update (\<lambda>h. h(p +\<^sub>p i := v)) s) p n = (arr_list s p n)[nat i := v]"
  using assms
  by (force simp add:
      list_eq_iff_nth_eq arr_list_to_heap_lookup fun_upd_def
      arr_list_length wellbehaved_pointers_def)

lemma arr_list_heap_update_comp:
  assumes
    "wellbehaved_pointers p n"
    "0 \<le> i"
    "nat i < n"
    "arr_is_valid s p n"
  shows
    "arr_list (heap_w32_update ((\<lambda>a. a(p +\<^sub>p i := v)) \<circ> f) s) p n = (arr_list (heap_w32_update f s) p n)[nat i := v]"
  using assms
  apply -
  apply (subst heap_w32_update_comp)
  apply (subst arr_list_heap_update)
      apply blast
     apply blast
    apply blast
    apply (simp add: arr_is_valid_update_heap)
  apply blast
  done

lemmas arr_list_heap_update_simps = arr_list_heap_update arr_list_heap_update_comp

(*******************************************************************************)

context reverse begin


section \<open> Reverse \<close>


(* The monadic definition that autocorres produces for the C code: *)
thm reverse'_def

subsection \<open> Reverse invariant \<close>

(* Hint: The invariant for the reverse function is split into three parts.
         In the following three definitions xs is the input list, 
         xs' is the modified list, and i, j are list indices. *)

(*  Replace True with the correct invariant in each of the following three definitions. *)

definition left_invariant :: "word32 list \<Rightarrow> word32 list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "left_invariant xs xs' i j \<equiv> \<forall>k. k < i \<longrightarrow> xs' ! k = xs ! (length xs - k - 1)"

definition middle_invariant :: "word32 list \<Rightarrow> word32 list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "middle_invariant xs xs' i j \<equiv> \<forall>k. i \<le> k \<longrightarrow> k \<le> j \<longrightarrow> xs' ! k = xs ! k"

definition right_invariant :: "word32 list \<Rightarrow> word32 list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "right_invariant xs xs' i j \<equiv> \<forall>k. j < k \<longrightarrow> k < length xs \<longrightarrow> xs'!k = xs!(length xs - k - 1)"

definition reverse_inv :: "word32 list \<Rightarrow> word32 list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "reverse_inv xs xs' i j \<equiv>
    left_invariant xs xs' i j \<and> \<comment> \<open> everything less than i is ...  \<close>
    middle_invariant xs xs' i j \<and> \<comment> \<open> everything between i and j is ... \<close>
    right_invariant xs xs' i j" \<comment> \<open> everything larger than j is ...  \<close>  

lemmas reverse_invariant_def = left_invariant_def middle_invariant_def right_invariant_def reverse_inv_def


(* Replace SOMETHING in the following lemmas by something that would allow you  
    to prove reverse_correct. *)


lemma left_invariant_step:
  assumes
    "length xs' = length xs"
    "i < length xs - Suc i"
    "middle_invariant xs xs' i (length xs - Suc i)"
    "left_invariant xs xs' i (length xs - Suc i)"
  shows
    "left_invariant xs 
    (xs'[i := xs' ! (length xs - Suc i),length xs - Suc i:= xs'! i])
    (Suc i) (length xs - Suc (Suc i))"
  using assms 
  unfolding left_invariant_def middle_invariant_def 
  apply clarsimp
  by (metis (no_types, hide_lams) less_imp_diff_less linorder_neqE_nat not_less_eq nth_list_update_eq nth_list_update_neq)

lemma right_invariant_step:
  assumes
    "length xs' = length xs"
    "i < length xs - Suc i"
    "middle_invariant xs xs' i (length xs - Suc i)"
    "right_invariant xs xs' i (length xs - Suc i)"
  shows
    "right_invariant xs 
    (xs'[i := xs' ! (length xs - Suc i),length xs - Suc i:= xs'! i]) 
    (Suc i) (length xs - Suc (Suc i))"
  using assms 
  unfolding middle_invariant_def right_invariant_def 
  apply clarsimp 
  proof -
    fix k :: nat
    assume a1: "length xs - Suc (Suc i) < k"
    assume a2: "\<forall>k>length xs - Suc i. k < length xs \<longrightarrow> xs' ! k = xs ! (length xs - Suc k)"
    assume a3: "k < length xs"
    have f4: "length xs - Suc i = k \<or> \<not> k < length xs - Suc i"
      using a1 by (metis (no_types) leq_minus_split less_Suc_eq_le nat_less_le not_less_eq)
    have "\<not> length xs - Suc i \<le> i"
      by (meson assms(2) less_Suc_eq_le not_less_eq)
    then have f5: "i \<le> length xs"
      by (meson i_hate_words_helper nat_le_linear)
    have f6: "\<not> length xs < i"
      by (meson assms(2) less_Suc_eq less_imp_diff_less not_less_eq)
    have "\<forall>n. n - Suc n = 0"
      by simp
    then show "xs'[i := xs ! (length xs - Suc i), length xs - Suc i := xs ! i] ! k = xs ! (length xs - Suc k)"
      using f6 f5 f4 a3 a2 by (metis (no_types) Suc_diff_Suc assms(1) assms(2) diff_diff_cancel length_list_update linorder_neqE_nat not_less_zero nth_list_update_eq nth_list_update_neq)
  qed

lemma middle_invariant_step:
  assumes
    "length xs' = length xs"
    "i < length xs - Suc i"
    "middle_invariant xs xs' i (length xs - Suc i)"
  shows
    "middle_invariant xs 
    (xs'[i := xs' ! (length xs - Suc i),length xs - Suc i:= xs'! i])
     (Suc i) (length xs - Suc (Suc i))"
  using assms unfolding middle_invariant_def by clarsimp 


text \<open> Show the precondition implies the invariant \<close>
lemma pre_impl_inv:
  assumes
    "n < UINT_MAX"
    "arr_is_valid s p n"
    "xs = arr_list s p n"
    "0 < n"
  shows
    "xs \<noteq> []"
    "reverse_inv (arr_list s p n) (arr_list s p n) 0 (n - Suc 0)"
  using assms
  unfolding reverse_inv_def left_invariant_def middle_invariant_def right_invariant_def
  by (auto simp add: arr_list_empty_iff arr_list_length)
   
text \<open> Show the invariant implies the postcondition \<close>

lemma left_all_is_rev:
  "left_invariant xs (rev(xs)) (length xs - 1) 0"
  unfolding left_invariant_def 
  by (simp add: nth_rev)

lemma 
  "i < length xs \<longrightarrow> left_invariant xs (rev(xs)) i (length xs -i -1)"
  unfolding left_invariant_def
  by (simp add: nth_rev)

lemma for_k_impl_rev:
  "length xs = length ys \<Longrightarrow>  \<forall>k. k < length xs \<longrightarrow> ys! k  = xs ! (length xs - k - 1) \<Longrightarrow> ys = rev xs"
  apply clarsimp
  apply (induct xs  arbitrary:ys )
  apply simp 
  by (metis length_rev nth_equalityI nth_rev_alt rev_rev_ident) 

lemma inv_impl_post:
  assumes
    "reverse_inv xs (arr_list s p (length xs)) r (length xs - Suc r)"
    "arr_is_valid s p (length xs)"
    "length xs - Suc r \<le> r"
  shows "arr_list s p (length xs) = rev xs"
  using assms
  unfolding reverse_inv_def left_invariant_def middle_invariant_def right_invariant_def
  apply clarsimp
  using for_k_impl_rev 
  by (smt arr_list_length diff_diff_cancel length_rev less_imp_diff_less linorder_neqE_nat
      nat_less_le nth_equalityI rev_nth) 
  

text \<open> Show the invariant is preserved by the loop \<close>
lemma invariant_preservation:
  assumes
    "i < length xs - Suc i"
    "arr_is_valid s p (length xs)"
    "reverse_inv xs (arr_list s p (length xs)) i (length xs - Suc i)"
  shows
    "reverse_inv xs
    ((arr_list s p (length xs))[i := xs ! (length xs - Suc i),length xs - Suc i:= xs! i])
     (Suc i) (length xs - Suc (Suc i))"
  using assms 
  unfolding reverse_inv_def left_invariant_def middle_invariant_def right_invariant_def
  apply safe 
    apply clarsimp 
    apply (metis (no_types, hide_lams) arr_list_length less_antisym less_imp_diff_less not_less_eq nth_list_update_eq nth_list_update_neq)
   apply simp 
  apply clarsimp 
  proof -
    fix k :: nat
    assume a1: "\<forall>k>length xs - Suc i. k < length xs \<longrightarrow> arr_list s p (length xs) ! k = xs ! (length xs - Suc k)"
    assume a2: "k < length xs"
    assume a3: "length xs - Suc (Suc i) < k"
    have f4: "\<forall>n na. \<not> (n::nat) \<le> na \<or> \<not> na < n"
      using less_Suc_eq_le not_less_eq by presburger
    then have f5: "length xs - Suc i = k \<or> \<not> k \<le> length xs - Suc i"
      using a3 by (metis (no_types) leq_minus_split)
    have f6: "i \<le> length xs"
      using assms(1) by linarith
    have f7: "Suc i \<le> length xs"
      by (meson assms(1) less_Suc_eq_le less_imp_diff_less not_less_eq)
    have "\<not> k \<le> i"
      using f5 f4 by (meson assms(1) le_trans nat_less_le)
      moreover
      { assume "length xs - k \<noteq> i \<and> k \<noteq> i"
        then have "(arr_list s p (length xs)) [i := xs ! (length xs - Suc i), length xs - Suc i := xs ! i] ! k = xs ! (length xs - Suc k) \<or> length xs - Suc i \<noteq> k \<and> k \<noteq> i"
          using f6 f4 a2 by (metis (no_types) arr_list_length diff_diff_cancel length_list_update leq_minus_split nat_less_le not_less_eq_eq nth_list_update_eq) }
      ultimately show "(arr_list s p (length xs)) [i := xs ! (length xs - Suc i), length xs - Suc i := xs ! i] ! k = xs ! (length xs - Suc k)"
        using f7 f5 a2 a1 by (metis (no_types) diff_diff_cancel nat_le_linear nat_less_le not_less_eq_eq nth_list_update_neq)
    qed

text \<open> Show reverse is correct \<close>

lemma inv_impl_mid: "reverse_inv xs xs' i j  \<Longrightarrow> middle_invariant xs xs' i j"
  unfolding reverse_inv_def by blast 

lemma mid_impl_access_origin: 
  "\<lbrakk>middle_invariant xs xs' i j ; ine \<ge> i ;  ine \<le> j\<rbrakk> \<Longrightarrow> xs ! ine = xs'! ine"
  unfolding middle_invariant_def by simp 


lemma state_access_is_arr_access: 
  "xs = arr_list s p n \<Longrightarrow> x < n \<and> x \<ge> 0 \<Longrightarrow> xs ! x = heap_w32 s (p +\<^sub>p int (x))"
  by (simp add: arr_list_to_heap_lookup)

lemma mid_impl_access_state_origin:
  "\<lbrakk>i < j; i \<ge> 0; j < n;length xs = n;xs' = arr_list s p n;
   middle_invariant xs xs' i j ; ine \<ge> i ;  ine \<le> j\<rbrakk>
   \<Longrightarrow> heap_w32 s (p +\<^sub>p int (ine)) =  xs ! ine "
  unfolding middle_invariant_def 
  by (simp add: arr_list_to_heap_lookup)

lemma mid_impl_access_heap : "\<lbrakk>
  i < j; i \<ge> 0; j < n;length xs = n;xs' = arr_list s p n;n < UINT_MAX;
   middle_invariant xs xs' i j ; ine \<ge> i ;  ine \<le> j; k \<ge>0 ; k < n \<rbrakk>
  \<Longrightarrow> xs [k := heap_w32 s (p +\<^sub>p int (ine)) ] = xs [k := xs ! ine]" 
  unfolding middle_invariant_def 
  apply clarsimp 
  by (simp add: arr_list_to_heap_lookup)

lemma pointer_add_simp:
  fixes r :: nat
    and s :: lifted_globals
  assumes a1: "r < length xs - Suc r"
  assumes a2: "n = length xs"
  assumes a3: "arr_is_valid s p (length xs)"
  shows "is_valid_w32 s (p +\<^sub>p (int (length xs) - (1 + int r)))" 
  proof - 
    have f4: "r < n - Suc r"
      using a2 a1 by meson
    then have "Suc r < n"
      by linarith
    then have f5: "\<not> n < Suc r"
      by linarith
    have "n - Suc r < n"
      using f4 by linarith
    then show "is_valid_w32 s (p +\<^sub>p (int (length xs) - (1 + int r)))"
      using f5 a3 a2 by (metis (no_types) add_diff_cancel_left' add_diff_inverse_nat arr_is_validD of_nat_Suc of_nat_add)
  qed 

lemma reverse_correct:
  "\<lbrace> \<lambda>s. wellbehaved_pointers p n \<and>
         length xs < UINT_MAX \<and>
         arr_is_valid s p (length xs) \<and>
         arr_list s p n = xs \<and>
         n = length xs \<and>
         n > 0
   \<rbrace>
       reverse' p n
   \<lbrace> \<lambda>r s. arr_is_valid s p (length xs) \<and> 
           arr_list s p n = rev xs \<rbrace>!"
  unfolding reverse'_def
  apply (wp | clarsimp)+
    apply (rule_tac
      I= "\<lambda> i s. 
        wellbehaved_pointers p n \<and>
        n = length xs \<and>
        n < UINT_MAX \<and>
        n > 0 \<and>
        i < n \<and>
        n - i - 1 < n \<and>
        arr_is_valid s p (length xs) \<and>
        reverse_inv xs (arr_list s p n) i (length xs - i - 1) 
      "
      and M = "\<lambda> (i,_) . length xs - i"
      in whileLoop_add_invI)
    apply (wp | clarsimp )+
      apply (auto simp add: arr_list_heap_update_simps)[2]
  using arr_is_valid_update_heap apply blast
       apply (frule invariant_preservation) 
         apply simp+
       apply (frule inv_impl_mid, subst heap_to_arr_list_lookup[where ?n = "length xs"], fastforce+) +
       apply (simp add: nat_minus_as_int reverse_invariant_def(2)) 
     apply (simp add: pointer_add_simp)
  using arr_is_validD apply auto[1]
  using reverse.inv_impl_post apply auto[1]
   apply (wp| clarsimp)
  using reverse.pre_impl_inv(2) by fastforce

end
