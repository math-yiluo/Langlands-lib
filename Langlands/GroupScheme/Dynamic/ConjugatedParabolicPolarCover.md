# Dynamic parabolic coverage after arbitrary diagonalization

This internal derived adapter combines `ConjugatedWeightedPolarIwasawa` with the
existing actual cocharacter diagonalization and dynamic subgroup comparison. It
extends `ParabolicPolarCover` by deriving the change of basis for every actual
cocharacter, while requiring adjoint stability only for the original matrix
representation. The base field and the `RCLike` coefficient field lie in an
arbitrary common universe `u`; the matrix index is any finite type in `Type`.

The existing `MatrixRepresentation.conjugate` composes a representation with the inner
automorphism of a genuine base point of the general linear group scheme.
`conjugate_affineMatrix` computes its affine point matrix as
`C ρ(x) C⁻¹`, where `C` is the coefficient matrix of the constant base point.
This identity holds for every coefficient algebra, without a topology assumption.

For the covering theorem, the representation is a closed immersion, its range on
actual coefficient points is adjoint-stable, and a supplied compact subgroup `K`
has a Hermitian represented right remainder `ρ(x z⁻¹)` for every actual point
`x`, with `z ∈ K`. Compactness uses the existing topology induced by evaluation of
all regular functions. The cocharacter `χ` is arbitrary; no simultaneous
adjoint-compatible diagonalization is assumed.

The existing `GeneralLinear.exists_innerIso_comp_eq_diagonalCocharacter` supplies
a base point and integer weights diagonalizing `χ ≫ ρ`. Compose `ρ` with this
inner automorphism to obtain a closed representation `ρ'`; the composite
cocharacter is now the actual diagonal group-scheme morphism. Its affine matrix
is `B⁻¹ ρ(x) B` for `B = C⁻¹`. Evaluate `χ` at the nonzero coefficient units
coming from `t_m = (1/2)^m`. The existing cocharacter evaluation formula then
gives the represented conjugate-diagonal sequence for these weights.

The two-limit covering theorem applies to the original adjoint-stable
representation and this arbitrary `B`. The existing dynamic-parabolic comparison
for `ρ'` identifies the resulting weighted block comap with the actual affine
point subgroup of `parabolic χ`. This proves
`parabolic_mul_compact_eq_univ_of_star_hermitian`, with the dynamic parabolic on
the left and the original `K` on the right.

If an actual group-scheme morphism `p : P ⟶ G` represents this dynamic parabolic,
its representing-range equality identifies that subgroup with the literal range
of `P.affinePointsTarget p`. Substitution proves
`range_mul_compact_eq_univ_of_star_hermitian`, retaining precisely that ordered
range-times-compact product on the actual coefficient point group.

The adapter introduces no external literature assertion. It does not construct
the original adjoint-stable reductive representation or the compact subgroup,
prove maximal compactness, or classify arbitrary geometric parabolics as dynamic
ones. These remain separate obligations for the full archimedean Iwasawa theorem.
