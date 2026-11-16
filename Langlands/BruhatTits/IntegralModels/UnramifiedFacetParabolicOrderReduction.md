# The full descended facet order bijection from upstairs radical generation

This internal reduction takes the existing exact proposition
`UnramifiedUpstairsRadicalRootGenerationStatement` as its sole global premise
and proves the unchanged `UnramifiedFacetParabolicOrderStatement`, at arbitrary
universe `u`. It retains the full host quantifiers and hypotheses of that target.

The generic transport lemmas show that the actual congruence subgroup is carried
by the rational-point isomorphism, so containment in another model's integral
points is preserved and reflected. For two incident characterized upstairs
models, the existing common-apartment reduction applies one simultaneous inner
transport. The full radical-generation bound puts the entire radical reduction
preimage inside the source's integral points. The target congruence subgroup is
contained in that preimage because its integral sections reduce to the identity.
Transport reflection gives the required containment for the original models.

The helper `unramifiedIncidentImageEmbedding_of_upstairs_rootGeneration` combines this containment with upstairs image parabolicity from the same generation premise.
The existing incident-image embedding theorem gives both parabolicity over the
original residue field and injectivity of the actual quotient-image map. The
arbitrary-facet attainment theorem supplies surjectivity onto every ground-field
parabolic subgroup functor. Finally, generic rigidity forces composition of the
supplied model morphisms, which makes incidence reverse image inclusion.

This is an internal composition of the named Library results, rather than a new
translation of a source passage. The source motivation of the unchanged target
is KP's incident-facet/parabolic correspondence; the implemented reduction uses
actual schematic images on all scheme tests. The reduction itself does not
assert its radical-generation premise unconditionally.

No no-inversions hypothesis is required: equality of quotient images already
recovers the two facets, whereas the final order clause asks only that incidence
implies reverse inclusion. The supplied family maps have the same identity
generic maps, so their composition is forced by generic rigidity.

The paired `UnramifiedFacetImageOrderDescent` and
`UnramifiedIncidentParabolicEmbedding` modules receive explicit names for their
local coefficient and residue-field instances. This avoids declaration-name
collisions when they are imported together with neutral-model descent. The
instances retain exactly their previous types and defining terms; their
mathematical statements and proofs are unchanged.
