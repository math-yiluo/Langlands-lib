# The congruence homomorphism to the Lie lattice quotient

`congruenceLieHom` is the canonical map from the actual level-`n`
congruence subgroup into the additive group of `(𝔪ⁿ L)/(𝔪ᵐ L)`,
written multiplicatively. Here `R` is a local domain with fraction
field `K`, `𝔪` is its maximal ideal, `M` is a smooth affine integral
model of the affine `K`-group `G`, and `L = M.lieLattice` is its
actual Lie lattice in `GenericLie R G`. The levels `n, m` are positive
naturals with `n ≤ m ≤ 2n`.

The generic congruence point determines a unique integral section by
`integralPointMap_injective`. Reduce this section by `reductionAt m`.
Its image under `congruenceTransition` is the identity since the section
has level `n`. The coefficient ideal `I` is the kernel of
`R/𝔪ᵐ → R/𝔪ⁿ`, canonically `𝔪ⁿ/𝔪ᵐ`. The inequality `m ≤ 2n` gives
`I² = 0`. The affine points comparison identifies the reduced section
with a point of `Lie.SquareZero.kernel` for `I`. Its image under
`Lie.SquareZero.kernelTensorAddEquiv` is the augmentation derivation,
viewed in `I ⊗[R] M.LieModule`. The comparison is additive for the
original multiplication of kernel points.

Smoothness makes the Lie module projective and hence flat. Tensoring the
inclusion of an ideal into `R` with this Lie module is injective.
Multiplication and `M.lieLatticeEquiv` identify its image with the ideal
times `L`. The quotients of these tensor products give
`congruenceLieTensorEquiv`. On the tensor of a class of `a ∈ 𝔪ⁿ` and a
model tangent vector `X`, it gives the class of `a • M.lieMap X`.

A level-`m` point reduces to the identity at level `m`. The resulting
kernel containment gives `congruenceLieQuotientHom` on the actual quotient
`G_n/G_m` by the universal property of the quotient group.

The construction follows Kaletha and Prasad, *Bruhat–Tits Theory: A New
Approach*, Proposition A.5.19(3) and Remark A.5.20, pp. 642–643 (PDF
pp. 673–674). It uses the base ring itself as the coefficient algebra.
The same construction works over the local domains in the congruence tower,
with their own maximal ideals. The proposition in the book also treats
flat test algebras over a discrete valuation ring.
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
