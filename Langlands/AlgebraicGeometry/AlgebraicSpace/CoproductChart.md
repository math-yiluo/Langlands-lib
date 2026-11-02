# Scheme coproduct charts over a fixed base

This internal module constructs the coproduct of a family of actual schemes
over a fixed base. `sigmaOver` takes the scheme coproduct and equips it with
the structure map induced by the components. The maps `sigmaOverι` and
`sigmaOverDesc` are the component inclusions and the induced map to a common
target. Their composition is the original component map (`ι_desc`).

The component inclusions are open immersions. A finite coproduct of affine
schemes is affine by Mathlib's scheme coproduct theorem. Local finite type of
the structure morphism is inherited from every component by its locality on
the source; this part works for an arbitrary indexing type in the scheme
universe.

`pullbackOpenCover` constructs the cover of a scheme over the base obtained
by pulling back the coproduct components, taking the fiber products in the
slice category. The standard comparison between slice and scheme pullbacks
transports joint surjectivity from the ordinary pullback of Mathlib's
coproduct open cover.

`isEtale_of_forall_ι` proves that a map from the coproduct scheme to a
presheaf with representable diagonal is etale if its restriction to every
component is etale. The diagonal hypothesis first gives representability of
the map. In each represented base change, the above open cover of the source
reduces etaleness to the etale projections of the component restrictions.
The proof pastes the pullback squares and applies locality of etaleness on
the scheme source.

These constructions and lemmas are internal derived content from the
imported algebraic-space interfaces, Mathlib's scheme coproduct and
pullback theorems, and source locality of the indicated morphism properties.
They impose no sheaf, finiteness, or quasi-compactness assumption on the
presheaf in the etaleness criterion.
