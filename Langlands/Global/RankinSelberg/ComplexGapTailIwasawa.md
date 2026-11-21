# Haar measure in the triangular tail

`complexGapTailIwasawa` expresses Haar measure on the trailing complex general linear group in the order compact factor, positive diagonal factor and upper unipotent factor. The unipotent measure is the product of the chosen scalar Haar measures on the strict upper entries. In the logarithmic diagonal coordinates, `tailModulus` contributes the product of the normalized absolute values of the upper root ratios. The formula retains a single positive constant for the normalizations of the compact, scalar and group Haar measures.

The proof starts from the right Iwasawa integration formula with unipotent entries before the diagonal. Moving the diagonal left replaces each entry in row `i` and column `j` by its multiple by `exp (y j - y i)`. The scalar Haar change of variables gives the inverse normalized absolute value of that multiplier. Finite product integration and the entry coordinate homeomorphism give the tail density. Haar uniqueness absorbs the initial change from Lebesgue measure to the chosen additive normalization into the constant.

This is the trailing-block measure calculation for the alternate expression of the split Godement integral. [Jacquet, *Archimedean Rankin–Selberg integrals*, Section 10.2, after (10.5)](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf).
