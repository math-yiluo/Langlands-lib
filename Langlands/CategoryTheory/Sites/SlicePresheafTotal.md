# Total presheaves over a slice base

This internal categorical construction changes the base of a presheaf on
`Over Q.left`, for an actual object `Q` over `T`. A section of `total Q G`
over an actual object `Z` over `T` retains a map `a : Z → Q` over `T`,
together with a section of `G` over the actual map `a.left`.
Restrictions compose the map to `Q` and apply the original restriction
map of `G`. The identity and composition laws follow from those of `G`.

`totalIso` applies a natural isomorphism to the section while retaining
the actual map to `Q`. Its naturality is the original naturality square.
This is an internal construction for expressing point fibres as total
Isom presheaves. It contains no geometric existence assertion.

If `R : Over Q.left` represents `G`, the representing object over `T` is
the actual composite `R.hom ≫ Q.hom`. The equivalence
`yonedaPointsEquiv` sends a lifted map `b : Z → R` over `T` to the base
map `b.left ≫ R.hom : Z → Q` and the same map `b.left` regarded over
`Q.left`. Its inverse forgets the intermediate base map and retains the
map into `R`; the two triangle equations establish that this is a map
over `T`. Extensionality of slice morphisms proves that these operations
are inverse. This equivalence commutes with every restriction map,
giving `totalYonedaIso` for the lifted Yoneda presheaves.

`representationIso` composes that natural isomorphism with `totalIso`.
Thus a natural representation of `G` on the entire slice over `Q.left`
gives a natural representation of `total Q G` on the entire slice over
`T`. No limits, nonemptiness, or smallness assumptions on the objects
are used. If the category has morphisms in `Type v` and `G` takes values
in `Type w`, its total presheaf takes values in `Type (max v w)`.

The provenance is internal: the module implements the dependent sum of
sections and the ordinary composition rule for representing objects
using Mathlib's actual slice category and lifted Yoneda functor. The
comparison is intended for the coherent-stack atlas construction; it
supplies no Isom-representability, smoothness, surjectivity, or atlas
existence theorem.
