void reverse(unsigned int a[], unsigned int n) 
{
    unsigned int temp;
    unsigned int i;
    unsigned int j;
    for (i = 0; i < n - i - 1; i++) {
        j = n - i - 1;
        temp = a[i];
        a[i] = a[j];
        a[j] = temp;
    } 
} 
