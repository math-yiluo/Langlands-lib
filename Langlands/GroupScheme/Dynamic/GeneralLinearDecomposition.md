# The limit, kernel and multiplication isomorphism on the GL block subgroup schemes

For any finite index type `n`, any commutative ring `R`, and any integer weights
`e : n → ℤ`, the concrete closed block schemes of
[`CorepresentedClosedSubgroup`](../CorepresentedClosedSubgroup.md) admit a split
limit homomorphism and a multiplication isomorphism:

`blockLimitHom : blockParabolicScheme → blockLeviScheme`,

`blockMultiplicationIso : blockUnipotentScheme ×_R blockLeviScheme ≅ blockParabolicScheme`.

The unipotent scheme is the actual scheme-theoretic kernel of `blockLimitHom`.
These conclusions concern the quotient schemes with the existing entry
equations and inclusions into the actual `GeneralLinear.groupScheme`.
There is no representation hypothesis in this module.

## Provenance and construction

This is an internal specialization of
[`SchemeDecomposition`](SchemeDecomposition.md) and
[`SchemeCoordinates`](SchemeCoordinates.md), using the three proved
representations in
[`GeneralLinearRepresentability`](GeneralLinearRepresentability.md).
Separatedness follows from the affine GL structure morphism.
The additional matrix formula uses the proved
`hasLimit_diagonalCocharacter_iff` from
[`GeneralLinearOrbit`](GeneralLinearOrbit.md). No new structural result from
the literature is asserted.

All declarations are in `Langlands.GroupScheme.GeneralLinear`.

- `blockLimitHom n R e` is the limit homomorphism for
  `diagonalCocharacter n R e`, expressed on the existing concrete schemes.
  `blockLimitHom_comp` identifies its ambient value with `Dynamic.limit`
  on every test scheme. `pointsEquiv_blockLimitHom` identifies the matrix of
  that value with the existing `blockLeviProjection` over
  `Γ(T, 𝒪_T)`. It follows from the all-test characterization of actual
  orbit limits.
- `blockLeviToParabolic n R e` is the block Levi inclusion.
  `blockLeviToParabolic_comp` proves compatibility with the two inclusions
  into GL. `blockLeviToParabolic_comp_blockLimitHom` proves the section
  identity as an equality of group-scheme homomorphisms.
- `blockUnipotentIsoKernel n R e` identifies the existing block unipotent
  group scheme with the Library's kernel of `blockLimitHom`.
  `blockUnipotentIsoKernel_hom_comp` proves compatibility with the ambient
  inclusions.
- `blockMultiplicationIso n R e` is an isomorphism in `Over (Spec R)`, with
  the unipotent factor first. `blockMultiplicationIso_hom_comp` and
  `lift_comp_blockMultiplicationIso_hom_comp` identify its morphism into
  GL with multiplication on universal projections and on arbitrary pairs
  of test points. Applying the published multiplicative GL point
  equivalence proves `pointsEquiv_blockMultiplicationIso_hom`, the
  ordinary matrix multiplication formula.
- `blockMultiplicationIso_inv_snd` identifies its inverse's block Levi
  coordinate with the actual `blockLimitHom`.
  `blockMultiplicationIso_inv_fst_comp` identifies its inverse's unipotent
  coordinate, followed into GL, with `p · (lim p)⁻¹`.
  Both are specializations of the proved scheme-coordinate identities.

The weights need not be distinct or ordered. There is no positivity or
nonemptiness requirement on `n`, no nontriviality condition on `R`, and no
field or reducedness assumption. All test schemes are retained.
The multiplication isomorphism is an isomorphism of schemes over the base,
with the specified multiplication formula; no direct product group
homomorphism, topology or Haar assertion is made.
