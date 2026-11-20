# Character twists of compact-open Hecke corners

Let \(K\) be a compact open subgroup and let \(\chi\) be a complex multiplicative
character trivial on \(K\). `characterTwist` sends \(f\) to the pointwise
product \(\chi f\) on the existing Hecke corner. The character is constant
on the open translates \(xK\), so the existing test-function multiplier
applies. Triviality on \(K\) preserves both invariances and fixes the
normalized indicator of \(K\). Inside the convolution integral,
\(\chi(y)\chi(y^{-1}x)=\chi(x)\), so multiplication by \(\chi\) preserves
convolution. On the double coset \(KgK\) the multiplier has the constant
value \(\chi(g)\), which gives `characterTwist_doubleCoset`.

This is the compact-open corner calculation used to implement the determinant
twist in the remark after Henniart–Lemaire (2011), I.6.11, printed p. 53.
