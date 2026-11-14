# Actual kernels in compatible binary multiplication cells

This internal construction concerns actual group schemes over an arbitrary base
scheme, with no field or smoothness assumption. Suppose homomorphisms
`q : G → H`, `f : U → V`, `g : P → R` commute with inclusions
`i : U → G`, `p : P → G`, `j : V → H`, and `r : R → H`.
The maps need not be closed immersions. Assume the ordered multiplication
`V × R → H` is a monomorphism of schemes over the base.

`kernelHom` constructs the induced homomorphism from each full scheme-theoretic
factor kernel to the full kernel of `q`. `multiplication` is the actual ordered
multiplication of these induced homomorphisms. `multiplication_ι` identifies its
ambient composite with the original multiplication after the two kernel
inclusions.

`isPullback` proves that this square is cartesian. For a point of the source
cell whose ambient image belongs to the kernel of `q`, compatibility and target
cell monicity force both target coordinates to be the unit. Each source
coordinate therefore lifts through its actual kernel pullback. The product of
these lifts solves the universal problem; the monomorphic kernel inclusions
give uniqueness. This uses all test schemes, including nonreduced tests.

Consequently `isOpenImmersion_multiplication` transfers an open-immersion
hypothesis on the source cell to the kernel cell by base change. It does not
claim that the kernel cell is surjective, nor that any dynamic factor quotient
exists or has smooth kernel.

The provenance is internal: the construction uses the published actual kernel
pullback, the published binary multiplication morphism, elementary cartesian
monoidal identities, and stability of open immersions under base change.
It supplies one geometric ingredient for the kernel-saturation argument of
Task 6404 and does not prove the host depth-zero opposite-factor statement.
