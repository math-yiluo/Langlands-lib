# Etale reduction of affineness to self-centralizing maximal tori

This internal reduction preserves the exact arbitrary-base and universe scope of
`ReductiveFiberAffinenessStatement`. It does not prove that statement
unconditionally. The two remaining inputs are explicit:

- smooth universal closed relative-torus families for smooth separated
  quasi-compact groups with affine actual residue fibres;
- affineness for a smooth separated quasi-compact group with connected reductive
  residue fibres and a supplied closed fibrewise maximal relative torus which
  represents its whole centralizer.

The first input has the exact type intended by
`TorusSubgroupModuli.SmoothAffineFiberTorusSubgroupRepresentabilityStatement`,
written explicitly here to avoid importing an unpublished statement. The second
is the remaining supplied-torus affineness case; a Weyl criterion together with
sufficient Weyl-quotient affineness would supply it. Neither input is established
by this module.

`EtaleSelfCentralizingTorusNeighbourhood.cover` converts an actual neighbourhood
at each base point into an etale cover indexed by those points. The supplied
point and its exact image equation prove joint surjectivity.
`isAffineHom_of_etaleSelfCentralizingTorusNeighbourhoods` then descends relative
affineness on the literal group pullbacks using the published
`RelativeLevi.property_of_etaleCover` and affine flat-descent instances.

`isAffineHom_of_universalTorusFamily_of_selfCentralizing` uses the imported
pointed-neighbourhood construction to obtain precisely this cover from a
supplied smooth universal torus family. Each cover member carries its actual
closed relative torus, literal fibrewise maximal inclusion and full all-test
centralizer representative. Applying the explicitly supplied local affineness
input on every member and descent gives affineness of the original group.

Finally,
`reductiveFiberAffineness_of_torusFamilies_of_selfCentralizing` applies the
universal-family input to the original group, using affineness of its actual
connected reductive residue fibres. Smoothness, separatedness and
quasi-compactness persist on the etale pullbacks, and
`connectedReductive_residueFibers_baseChange` supplies their connected reductive
actual residue fibres. The supplied-torus input therefore applies on each
member, proving the exact original proposition under the two stated inputs.

The provenance is internal composition of actual neighbourhood construction,
base-change geometry and etale descent. No base restriction or global
ambient-affineness hypothesis is inserted, and no external-source theorem is
claimed as proved here.
