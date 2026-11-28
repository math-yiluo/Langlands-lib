# Dirac testing on orthogonal polynomial layers

The module proves `orthogonalDiracConvolution` of type
`OrthogonalDiracConvolutionStatement`. Let `H` be a finite group with a
homomorphism `s : H → O(n)` and a character `χ : H → ℂˣ`. The bilinear
pairing and left convolution use the same finite left-invariant Borel measure
on `O(n)`. Suppose the continuous kernel is left covariant for `χ`, and its
pairing with each inverse-character test `ψ` of Lipschitz constant `L ≥ 0`
differs from `ψ(1)` by at most `δ (‖ψ‖∞ + L)`, where `δ ≥ 0`. The
Lipschitz condition uses the inherited row-sum matrix norm. On the
character-covariant profiles of entry degree at most `N`, left convolution
then differs from the identity by at most `δ C_n (1 + N)^2` in supremum
operator norm, with `C_n > 0` depending only on `n`.

At an output point `z`, project the test `x ↦ u(x⁻¹ z)` to the inverse-character
space using `finiteCharacterAverage`. Kernel covariance absorbs the character
weight of each summand into the kernel, and left invariance of the measure
permits the substitution `x ↦ s(a)x` in its integral. Thus the projection
preserves the pairing. Covariance of `u` gives the projected value `u(z)` at the
identity. The projection is contractive in the supremum norm. For the Lipschitz estimate,
submultiplicativity of the matrix norm bounds the distortion under inversion and
right multiplication uniformly on the compact orthogonal group.
`orthogonalPolynomialLipschitz` then gives a Lipschitz constant at most a
rank-dependent multiple of `(1 + N)^2 ‖u‖∞` for the projected test. Applying the
Dirac estimate at every output point proves the asserted operator bound.
