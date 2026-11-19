# Estimates for the actual dynamic conjugation split

`RationalDynamicConjugationHeightBounds` records two inequalities for the
actual split cell at a compact open subgroup. The complement compares the
height of the conjugator with the heights of the group element and its
conjugate. On the opposite radical, inverse conjugation outside the compact
open subgroup gives a lower bound proportional to one plus the height of
the conjugator.

The analytic estimate uses the Haar measures in
`rationalConjugationPairing_eq_dynamic_split`. The opposite Haar modulus is
the reciprocal of the forward one by the dynamic reciprocity theorem. The
Schwartz seminorms and weighted Xi-square estimate give convergence of the
original integrand for all conjugators. Compact averaging with the ambient
height envelope gives the complement estimate.

For the open cell, the forward constant-term estimate bounds the second
factor. Vanishing of the full opposite constant term replaces the truncated
first factor by its tail. The product-height comparison and the cutoff
extract arbitrary powers of the height of the conjugator. The output
constant-term weights use the restriction of the ambient height envelope.
Levi compact averaging and the Levi Xi bound yield the claimed decay with the
original height and the stated ambient half-weight. The norm inequality for
the integral split combines the two estimates.

This is a derived assembly for Waldspurger's 2003 Plancherel article,
VIII.3.1, printed pp. 323–326. It takes the local Xi and constant-term
estimates, the two geometric inequalities, the product-height comparison,
the half-weight comparison and vanishing on the opposite radical as inputs.
