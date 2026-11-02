# Actual coherent-family point fibres from product-base Isom schemes

This internal construction specializes `Stacks.PointFiberRepresentability`
to the published actual family-groupoid pseudofunctor and its explicit
morphism-universe lift `PseudofunctorHomLift.homLift.{u + 1}`. It preserves
the scheme universe `u`, ordinary pullback functors, actual family
objects and isomorphisms, and every test scheme in the full slice.

For families `M` over `U` and `N` over `T`, `productIsomComparison`
identifies the product Hom presheaf with
`FamilyGroupoid.isomPresheaf` of their pullbacks along the two projections
from `U × T` in `Over S`. This comparison is definitionally the identity:
the two definitions use the same lifted pseudofunctor Hom presheaf and
the same iterated-slice reindexing. The lifted fibre categories are
groupoids because the original family categories are cores and the
morphism lift is a category equivalence.

Given an actual `I` over the underlying product scheme and a natural
representation of that Isom presheaf by `I`, `pointFiberIsomSchemeIso`
uses the general scheme-slice adapter to represent the entire actual
coherent-family point-fibre presheaf. The representing scheme is
`Stacks.pointFiberScheme I`; its map to `T.left` is the composite of
`I.hom` and the underlying second projection. This is a natural
isomorphism of full presheaves, including all restriction morphisms.

`exists_pointFiberIsomScheme_of_properIsom` is a conditional consequence
of the exact published proposition `ProperIsomRepresentabilityStatement`.
Assuming that proposition, properness and local finite presentation of
`f`, it applies the proposition at the product test base and to the
two actual pulled-back families. It retains the resulting affine,
locally finitely presented map `I.hom` to the product and applies the
preceding natural comparison. Affineness and local finite presentation
here concern `I.hom`, rather than its composite map to `T.left`.

The provenance is internal: this is a direct comparison of existing
presheaf definitions followed by a conditional application of the
published proper-Isom statement. This unit does not prove that
statement. It establishes no smoothness, surjectivity, locally finite
type atlas, or unconditional atlas existence. The proper-Isom proof
and the construction of a smooth surjective presentation remain
separate obligations.
