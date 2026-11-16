# Parabolic order bijection for descended unramified facet models

`Langlands.BruhatTits.IntegralModels.unramifiedFacetParabolicOrder` proves the
existing `UnramifiedFacetParabolicOrderStatement.{u}` at arbitrary universe
`u`. Its type retains all seven building hypotheses, all eight apartment
descent hypotheses, every supplied model and auxiliary datum, and the
characterization of every facet model by its maximal-unramified integral
points. The conclusion concerns the actual schematic-image subgroup
functors in the supplied reductive quotient over the original residue
field.

The proof applies
`unramifiedFacetParabolicOrder_of_upstairs_rootGeneration` to
`unramifiedUpstairsRadicalRootGeneration`. The latter proves the full
upstairs radical-generation proposition: one common centralizer subgroup,
chosen before the facet subsets and models, together with positive root
fixers generates the entire actual radical reduction preimage. Its proof
uses singleton generation and constancy on nonempty subsets of a facet,
with the common subgroup supplied by the torus-centralizer radical
comparison.

The applied reduction uses this generation theorem after simultaneous
transport of incident models to a common apartment. The target's
congruence subgroup lies in the radical reduction preimage because its
sections reduce to the identity. The generation bound therefore puts it
inside the source's integral points. Together with upstairs image
parabolicity, this gives descended parabolicity and recovery of the
incident facet from its actual quotient image. Arbitrary-facet attainment
gives surjectivity onto all ground-field parabolic subgroup functors.
Finally, generic rigidity forces composition of the supplied model maps,
so facet incidence implies reverse inclusion of the images. The resulting
map satisfies exactly the target's `Set.BijOn` and incidence clauses.

The source motivation is KP Axiom 4.1.22(5), through the descended
incident-facet correspondence and passage to the maximal reductive
quotient. The unchanged statement Markdown records the original sources,
corrections, hypotheses and precise scope. This proof is an internal
composition of the named Library results; its implemented route is the
radical-generation reduction described above. The order clause has the
published direction: incidence implies reverse inclusion. No converse
order implication is asserted.
