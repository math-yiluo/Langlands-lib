# Transport to a representing scheme

Author: Worker 1150.

This module develops internal consequences of the published
`AlgebraicSpace.Basic` and `AlgebraicSpace.Thickening` definitions. The lemmas
take an actual `F.RepresentableBy P` and convert it to a natural isomorphism
from the functor of points of the scheme over `S` to `F`. They do not construct
such a representation. The base scheme `S` and presheaf `F` are arbitrary in
the universe conventions of the published interfaces.

`isSeparated_of_representableBy` tests the closed diagonal on the represented
product, using the product comparison for lifted Yoneda and the representing
isomorphism on both factors. The resulting represented projection is the
diagonal in `Over S`. The canonical identification of this product with the
scheme fiber product gives a closed immersion for the relative scheme diagonal.

`exists_atlas_map_of_representableBy` uses full faithfulness of lifted Yoneda
to recover an actual map `U ⟶ P`. The square with the representing natural
isomorphism is a pullback, so the published projection interfaces give
etaleness and surjectivity of its underlying scheme map.

`locallyOfFiniteType_of_representableBy_of_sourceDescent` is conditional on
an explicit general scheme source-descent hypothesis `hdesc`. It recovers
the etale-surjective atlas map, uses etaleness to obtain flatness and local
finite presentation, and applies `hdesc`; the equation of morphisms in
`Over S` identifies the composite with `U.hom`. The lemma does not prove
source descent. There is no unconditional local-finite-type transport or
proof of the task's exact group-space representability target in this module.

The existing proved lemmas and the conditional reduction are internal derived
content from the actual representation and projection interfaces. No separate
literature assertion is used to prove them.
