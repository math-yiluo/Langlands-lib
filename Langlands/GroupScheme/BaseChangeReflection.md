# Reflection of group-scheme isomorphisms under fpqc base change

Worker 1340.

This internal helper specializes Mathlib's faithfully flat descent of
isomorphisms to the published group-scheme base-change construction.
It uses no external structural theorem about reductive groups or tori.

For a surjective, flat, quasi-compact morphism `b : S' ⟶ S`,
`isIso_of_baseChange b f` proves that a given group-scheme homomorphism
`f` is an isomorphism when its base change is an isomorphism.
The proof identifies the square of the underlying scheme maps as
cartesian. The target projection is a base change of `b`, so it is
again surjective, flat and quasi-compact. Mathlib's fpqc descent of
scheme isomorphisms applies to this square. The forgetful functor
from schemes over `S` reflects isomorphisms. The proof then lifts this
underlying isomorphism to group objects using `Grp.mkIso'`; its forward
map is the given group homomorphism `f`.

`isoOfBaseChange b f` records the resulting actual group-scheme
isomorphism, whose forward map is exactly `f`, as stated by
`isoOfBaseChange_hom`. This construction concerns a homomorphism already
defined over `S`; an arbitrary isomorphism between the base-changed
objects is not a sufficient input.

`fieldExtension_fpqc k K` proves that an arbitrary field extension
of the same universe supplies a surjective, flat, quasi-compact
map on spectra. It uses faithful flatness of a nonzero vector space
over a field and affineness of the spectrum map.
