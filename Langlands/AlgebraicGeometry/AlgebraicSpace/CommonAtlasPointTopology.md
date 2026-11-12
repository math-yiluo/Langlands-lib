# Point comparisons under restriction of the scheme base

This internal supporting module compares points of presheaves over schemes
`T` and `S`, where `g : T → S` is any morphism. It proves a homeomorphism
criterion using a common surjective étale scheme chart. It does not assert
limit descent or construct such a chart for every restricted presheaf.

`forgetBaseYoneda g U`, for a scheme `U` over `T`, forgets the structure map
to `T` in every morphism to `U`. Its target is the restriction of the presheaf
represented by `U` viewed over `S`. The comparison is natural in `U`.

`FieldPoint.forgetBase` retains the field and section of a restricted
presheaf point, and composes its structure map with `g`. The common-field
relation is preserved, so this descends to `Points.forgetBase g F` from
points of the restricted presheaf to points of `F`. This map is natural in
transformations of `F`. After composition with `forgetBaseYoneda`, it sends
the canonical residue-field point of `U` to the canonical point of the
same underlying scheme viewed over `S`. Consequently it carries a chart's
point map to the original chart's point map. Evaluation at the identity
of `U` shows that a chart over `S` is determined by this restricted
transformation from `h_U` over `T`.

The criterion `sameImage₂_forgetBase_iff` has the following explicit data:

- A presheaf `F` over `S`, a presheaf `C` over `T`, and a monomorphism
  `v : C → restrictPresheaf g F`.
- A single scheme `U` over `T` with charts `a : h_U → C` and
  `b : h_(U over S) → F`, whose transformations commute with `v` and
  `forgetBaseYoneda`.
- A transformation `rho : F → h_(T over S)` such that `b ≫ rho` is exactly
  the represented structure morphism `U → T`.

Under these hypotheses the common-test-scheme relation `SameImage₂` on
points of `U` is identical for `a` and `b`. A witness over `T` gives a
witness over `S` by forgetting the structure map. Conversely, composing a
witness equality with `rho` shows that its two maps to `U` induce the same
map to `T`. Equip the witness scheme with that structure map. The resulting
maps to `U` lie over `T`; their chart transformations agree after `v` by
naturality and the original witness equality, hence agree because `v` is
monic. This constructs a witness over `T` with the same ordinary points.
No étaleness or surjectivity is needed for this relation comparison.

`forgetBasePointsHomeomorph` additionally requires both charts to be étale
and surjective in the published relative scheme-property sense. Its forward
function is `Points.forgetBase g F ∘ Points.map v`. The atlas point maps
are surjective and commute with that function. Their fibre relations agree
by the preceding result and `chartPointMap_eq_iff_sameImage₂`, which proves
bijectivity. Each atlas point map is a quotient map for its presheaf's
`pointTopology`. The commuting identities therefore prove continuity of
the bijection and its inverse.

The provenance is internal: all constructions and proofs are derived from
the published definitions of field points, common-field equivalence,
restriction and the existing atlas quotient topology and common-test
relation. No external assertion is added. This is supporting infrastructure
for the remaining properness and geometric-fibre clauses; those clauses of
`SpaceLimitPropertyDescentStatement` remain open.
