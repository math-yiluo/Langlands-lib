# The integral facet torus in the reductive quotient

This derived adapter concerns an arbitrary supplied relative-component model
`D` over a local domain `R` with fraction field `K`, a supplied integral torus
`T`, and a supplied special-fibre quotient `Q`. It assumes `T.IsClosedSplit`
and `Q.IsReductiveQuotient`. It needs no building or facet hypotheses and
does not assert the existence of these data.

`IntegralTorusData.isClosedSubgroup_quotientTorus` proves that the actual
composite `T.specialFibreInclusion ≫ Q.projection` is a closed subgroup
inclusion. The radical representative is affine because it is closed in the
affine neutral special fibre. Its smoothness, and the connected reductivity
of the quotient, supply local finite type. Base change gives a closed split
special torus. The represented fppf quotient predicate identifies its full
scheme-theoretic kernel with the radical image on every test scheme.
The published `IsUnipotent.closed_torus_quotient`, applied with
`unipotentClosedSubgroup`, then gives closedness.

`IntegralTorusData.quotientTorusImageIso` constructs an isomorphism from the
actual special torus to the schematic image of the same composite, using
`IsUnipotent.torusQuotientImageIso` with those same data. Its homomorphism is
the canonical schematic-image projection, as stated by
`quotientTorusImageIso_hom`; composing it with the image inclusion recovers
the original quotient-torus map, as stated by
`quotientTorusImageIso_hom_inclusion`.
These image declarations carry an affine-structure-map instance for the
integral torus, so that the schematic image can be formed in their types.
This instance follows from the closed inclusion into the affine neutral
model; it is not needed as a separate hypothesis of the closedness theorem.

The provenance is a composition of the published closed-unipotent-subgroup
theorem, the unipotent-kernel torus image construction, and base-change
stability of closed subgroups and split tori. The adapter does not establish
maximality of the quotient torus, identify quotient roots, or construct
reflection representatives. Those remain separate geometric obligations
for the unramified facet root-datum theorem.
