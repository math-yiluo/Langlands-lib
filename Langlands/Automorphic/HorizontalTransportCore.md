# Transport of actual horizontal cochains by full operator intertwiners

For a number field `F : Type u` and actual full operator realizations
`S`, `T`, `U : OperatorRealization F n`, this internal construction transports
the existing horizontal full-compact-equivariant cochains with complex
coefficients in their actual spaces. The number-field universe is arbitrary.
Transport, its finite equivariance, and its identity and composition laws
allow every natural rank and cochain degree, including zero. Differential
naturality requires positive rank, as does the imported actual horizontal
differential; its degree is still arbitrary.

For `A : S.Intertwiner T`, `Intertwiner.horizontalMap A q` has source
`S.horizontalFiniteRepresentation q` and target
`T.horizontalFiniteRepresentation q`. Its underlying complex-linear map is
`horizontalMapCoefficients F n q A.compactRestriction`. Thus it postcomposes
each coefficient value by the same actual full operator intertwiner `A`.
The existing coefficient map preserves vanishing whenever any argument is
in the actual compact image and equivariance for every element of the full
standard infinite compact group. The finite intertwining equation follows
pointwise from `A.finite`; no new covariance hypothesis is supplied.

`horizontalMap_apply` identifies the coefficient at a reduced Lie tuple
`X` with `A (f.val X)` by reflexivity. `horizontalMap_id` and
`horizontalMap_comp` are equalities of the bundled finite adelic
intertwiners. Subtype and alternating-map extensionality reduce them to the
identity and composition of coefficient maps, proved by reflexivity. In the
composition formula `B.comp A`, the map `A` is applied first.

`horizontalMap_differential` states
`A.horizontalMap (q + 1) (S.horizontalDifferential q f) =
T.horizontalDifferential q (A.horizontalMap q f)`.
Subtype extensionality reduces this equation to the existing coefficient
`map_differential` theorem applied to `A.reducedLieRestriction`. That
restriction retains `A`'s same linear map and its proved compatibility with
the actual reduced differential action. `horizontalMap_differential_comp`
expresses this naturality square as an equality of finite adelic
intertwiners, using the existing `horizontalDifferentialIntertwiner` and
linear-map extensionality.

The provenance is internal restriction and postcomposition from the
published `OperatorEquivalence`, `OperatorCompactCompatibility`,
`ArchimedeanHorizontal`, `HorizontalDifferential`, `HorizontalFiniteAction`
and `HorizontalDifferentialFinite`, together with coefficient naturality
in `Cohomology.Lie.CoefficientCochains`. This unit makes no new external
source identification. It constructs transport on the given concrete
coefficient spaces; square zero, cycles, boundaries, cohomology, smoothness
of the horizontal representation and general tensor coefficients remain
separate obligations.

Authorship: Worker 2.
