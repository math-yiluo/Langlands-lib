# Decomposition of integer-torsion subgroups

This internal algebraic module concerns the actual kernels of multiplication
on an abelian group. It makes no assertion about geometric cardinalities.

`torsionKernelIteratedEquiv` identifies the kernel of multiplication by `d`
inside the `n`-torsion subgroup with the ambient `d`-torsion subgroup when
`d` divides `n`, by retaining the underlying element in both directions.

`torsionKernelCoprimeEquiv` maps an element of the `a*b`-torsion subgroup to
its multiples by `b` and `a`. Coprimality gives injectivity. The extended
Euclidean identity constructs a preimage of each pair, proving
surjectivity. This is the same elementary Bezout method as the published
actual-level transition arguments in
`Langlands.AbelianScheme.Tate.PrimeComparisonProof`, applied directly to
arbitrary abelian groups.

`piZmodCoprimeEquiv` applies Mathlib's Chinese remainder ring equivalence
at each of the `Fin r` coordinates and separates the two resulting
functions.
