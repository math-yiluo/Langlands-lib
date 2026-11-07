# Restricting radical-free root centralizers

Author: Worker 1465.

This internal support unit transfers actual cocharacter centralizers from an
ambient group to a closed subgroup containing them. It is uniform in universe
`u`, retains all scheme tests, and assumes no reductivity theorem for a fixed
subgroup or affine homogeneous quotient.

`Dynamic.isRepresentedBy_factorHom_centralizer` starts with a monic inclusion
`q : M → G`, a cocharacter of `M`, and an actual ambient representative
`l : L → G` of its centralizer. If the full range of `l` is contained in the
range of `q`, the canonical factor `L → M` represents the internal centralizer.
The proof uses the published all-test centralizer comparison under a
monomorphism and cancellation through `q`.

`RadicalFreeRootCentralizerData.restrict` transfers the existing rootwise
record through this factor. Its cocharacter, group, annihilation equation and
trivial-radical proof are unchanged.

`isConnectedReductive_of_contained_rootCentralizers` applies that construction
over an algebraically closed field. A smooth connected affine closed subgroup
containing a split self-centralizing torus is connected reductive if, for
each of its actual roots, it contains an ambient radical-free cocharacter
centralizer annihilating that root. The proof applies the published
`RadicalFreeRootCentralizerData.isConnectedReductive` to the transferred data.
All rootwise witnesses and containments remain explicit premises.

The provenance is internal composition of the existing represented-subgroup,
dynamic-centralizer restriction and rootwise radical-detection constructions.
This unit does not yet prove the full-kernel centralizer reductivity statement.
