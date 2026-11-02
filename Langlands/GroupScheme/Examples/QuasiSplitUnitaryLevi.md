# The diagonal map for the quasi-split quadratic unitary group

This module implements definition unit 4.
For fields `F`, `E`, an `F`-algebra structure on `E` and
`IsQuadraticExtension F E`, it allows every `F`-automorphism `c` of `E`.
The intended quadratic-unitary specialization takes `c` nonidentity.
It imposes no characteristic restriction.

For every commutative `F`-algebra `R`, `leviDiagonalMatrix R c a` is the
invertible matrix `diag(a,c_R(a⁻¹))`, for a unit `a` of `E ⊗[F] R`.
Its inverse is `diag(a⁻¹,c_R(a))`. Here `c_R = c ⊗ id`, and
`c_R(a⁻¹)` is the inverse of the unit `c_R(a)`.
`leviDiagonalUnitary R c` packages the formula as a group homomorphism
to the full unitary matrix subgroup `matrixPoints R c`.
`leviDiagonalUnitary_val` records its entries.
`leviDiagonalUnitary_injective` recovers the parameter from the first
diagonal entry and proves injectivity.

`tensorCoefficientMap_scalarConjugation` proves that changing the right
tensor factor commutes with conjugation on the left factor, by tensor
induction. `leviDiagonalUnitary_naturality` then proves that the matrix
homomorphism commutes with every change of coefficient algebra.

The formula is derived from the antidiagonal hermitian presentation:
`diag(a,c_R(a)⁻¹)` satisfies the full unitary equation.
Milne, *Algebraic Groups* (2017), Proposition 24.40,
Definition 24.42 and Theorem 24.44, printed pp.523–525, provide the
unitary algebra-involution framework. The last theorem concerns special
unitary groups; this construction uses the Library's full unitary group.

The source of the scheme homomorphism is the published
`WeilGm.groupScheme (CommRingCat.of F) E`, the Weil restriction
`Res_{E/F} 𝔾ₘ`. A quadratic field extension is finite projective as an
`F`-module, so this host construction applies. Its point equivalence,
composed with `leviDiagonalUnitary` and the inverse of the existing
unitary `pointsEquiv`, defines `leviPoints b c T`. Thus both source and
target are the existing Library group schemes.

`leviPoints_naturality` combines the two point-equivalence naturality
theorems with coefficient naturality of the diagonal matrix map.
`leviHom b c` applies `homOfPoints` to this natural family of group
homomorphisms. `pointsEquiv_leviHom` proves its formula over every test
scheme, including non-affine and non-reduced schemes: a tensor unit `a`
maps to `diag(a,c_R(a)⁻¹)`, with `R` the global-sections algebra.
The `homOfPoints` construction and these formulas are internal
consequences of the represented point models.

Identification with the dynamic centralizer and closedness are reserved
for the separate `LeviRepresentedStatement` and its proof task.
