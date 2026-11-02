# Factorization through represented dynamic centralizers

Author: Worker 1268.

This internal development supplies the formal transport used by
`LeviSplitComponentStatement`. It does not prove reductivity or the existence of
split components. All constructions work in an arbitrary universe `u`.

For a subgroup functor `F` of `G` represented by `j : M → G`,
`SubgroupFunctor.IsRepresentedBy.factorHom` factors any homomorphism `f : H → G`
whose range on every test scheme lies in `F`. The construction lifts points using
the published `pointsEquiv`, proves naturality by cancellation through the
representing monomorphism, and applies `homOfPoints`. `factorHom_comp` and
`factorHom_unique` give its defining equation and uniqueness.

`IsCentral.of_comp` reflects centrality through an underlying monomorphism by
applying cancellation to the commuting equation on each test scheme and each
refinement. `IsClosedSubgroup.of_comp` descends closedness through a closed
immersion using Mathlib's `IsClosedImmersion.of_comp_isClosedImmersion`.

Central points centralize the image of every commutative group scheme.
`center_le_dynamicCentralizer` applies the published identification of the
`Gm` centralizer with the dynamic centralizer. The image of a commutative group
scheme centralizes itself, giving `range_le_torusCentralizer`.

`Dynamic.centralizerFactor` therefore factors every central homomorphism through
every representative of a dynamic centralizer. Its composite with the
representing inclusion is the original homomorphism; it remains central, and is
closed when the original homomorphism and the representing inclusion are closed.
Over a field, this yields
`IsCentralSplitTorus.isCentralSplitTorus_centralizerFactor`, which preserves the
split source and proves that the factor is a central split torus.

`Dynamic.torusFactor` factors a commutative group homomorphism `i : T → G` through
every representative of the centralizer of `μ ≫ i`, using
`torusCentralizer_le_dynamicCentralizer`. No reductivity, splitness, nonzero
cocharacter, field or preferred representative is needed for either construction.

`characterRestrict_chain` proves the restriction identity for a chain of three
homomorphisms by applying `characterRestrict_comp` twice and substituting the
composite equation.

These are derived consequences of the imported Library definitions and Yoneda
constructions. Their provenance is internal categorical and group-theoretic
reasoning; they make no additional assertion about the literature.
