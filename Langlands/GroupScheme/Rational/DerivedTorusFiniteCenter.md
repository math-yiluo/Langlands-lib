# The full finite centre from a derived-torus complement

This internal construction uses the actual central-product homomorphism in
`DerivedTorusCentralProduct`, the published finite central-intersection proof,
and the full-centre comparison under an epimorphic central product. Its hypotheses
include a supplied `DerivedTorusCentralComplement e i`, an actual derived inclusion
`d : D ⟶ G` of a connected reductive group over any field, a compatible torus map
`j`, and scheme surjectivity of `subgroupProductMap d i`. It does not prove the
existence of an ambient root datum or the latter surjectivity assertion.

`flat_centralProduct_of_finiteType` requires only smoothness of the ambient group,
local finite type and quasi-compactness of the subgroup. The actual source product
has these last two properties by base change and composition, using splitness of
the complement torus. The published `flat_of_surjective` theorem then proves
flatness of the actual group homomorphism.

`epi_subgroupProductMap` uses flatness and scheme surjectivity to obtain a scheme
epimorphism, lifts it to the category over the field, and applies the exact equality
`centralProduct_hom`. For an actual derived subgroup, smoothness follows directly
from the published smooth connected commutator construction and affineness from
the closed inclusion. Thus `epi_subgroupProductMap_of_derived` has no derived
reductivity or semisimplicity premise.

`center_eq_comap_of_derived` identifies the full derived centre with the inverse
image of the full ambient centre on every test scheme. The published
`derivedCentralIntersectionFiniteness` supplies a finite closed representative of
that inverse image. The full-centre comparison reinterprets this same representative
as the entire centre of `D`, giving `hasFiniteCenter_of_derived`.
`finiteDerivedCenter` chooses the resulting actual finite group scheme and its
closed inclusion, retaining the full-centre representation proof in `FiniteCenter D`.
No reduction of the centre or restriction to field-valued points occurs.

`isSemisimple_of_derived` combines this finite centre with the published connected
reductivity theorem for actual derived subgroups. Finally,
`IsDerivedSubgroup.isSemisimple_of_rootDatum_product` constructs the complement
from the supplied actual ambient root datum and compatible maximal split tori,
and applies this consequence. All field and universe parameters remain arbitrary.
This is a conditional supporting result, not an unconditional proof of the global
derived semisimplicity statement or the host Levi cocenter root-model statement.

The provenance is internal: the module composes the named actual constructions
and comparison results. Worker 1367 contributed the observation that the flatness
and epimorphism step needs only the source finiteness properties, which derived
smoothness and the closed immersion supply without using derived reductivity.
