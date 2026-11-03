# Base change of actual homogeneous quotients

This internal construction uses the published
`HomogeneousQuotientFromEmbedding.HomogeneousQuotient` record. It works over
arbitrary morphisms of base schemes in an arbitrary universe. No field,
smoothness of the subgroup, or reductivity hypothesis is needed beyond the
data already supplied by that quotient record.

For an actual quotient `Q` of a homomorphism `i : H ⟶ G` and a base morphism
`b : S' ⟶ S`, `HomogeneousQuotient.baseChange b Q` has scheme
`Q ×[S] S'` and projection given by pulling back the original projection.
Its subgroup homomorphism is the actual base change of `i`.

Separatedness, local finite type, and quasi-compactness of the structural
morphism follow from stability under base change. The same stability gives
smoothness, surjectivity, and quasi-compactness of the projection. For every
scheme `T` over `S'`, the pullback adjunction identifies its maps into the new
quotient with its maps into the original quotient when `T` is regarded over
`S`. Naturality identifies the composites of the projection under that
equivalence. The original fiber criterion then applies. The multiplicative
pullback point equivalence preserves inverse and product, and
`SubgroupFunctor.range_baseChangeHom` identifies the actual subgroup ranges.
This proves the required right-coset fiber criterion on all scheme tests,
including nonaffine and nonreduced tests.

`baseChange_projection_fst` gives the commutative square of the projection
with the canonical morphisms to the original schemes.
`baseChange_isAffineHom` proves that affineness of the supplied actual
quotient is preserved by arbitrary base change.

All content is derived from the published quotient record, the pullback
adjunction, and the published subgroup base-change identities. This helper
supplies quotient transport for geometric arguments. It does not establish
the affine-quotient reductivity criterion or construct an affine quotient
for a character-kernel centralizer.
