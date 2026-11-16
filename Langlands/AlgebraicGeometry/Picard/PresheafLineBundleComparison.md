# Universal line bundles under changes of presheaf and representer

Let `F` and `G` be presheaves on the full slice of schemes over a scheme
`S`, with values in `Type v`, and let `L : PresheafLineBundle F` be coherent
actual line-bundle data. The scheme universe `u` and the value universe `v`
are arbitrary.

`universal_reindex_ofIso` states that reindexing `L` along a presheaf
isomorphism `φ : G ≅ F` and evaluating at a representation `e` of `G`
gives exactly the same line bundle as evaluating `L` at `e.ofIso φ`.
This is a definitional equality of the evaluated families.
Conversely, `universalOfIso` transports a representation of `F` to `G`
and reindexes `L` along the inverse isomorphism. The resulting line bundle
is isomorphic to the original one by the inverse law for `φ`.

More generally, `universalReindexIso` takes a natural transformation
`φ : G → F` and supplied representations of both presheaves. It uses the
representation of `F` to classify the image of the universal `G`-family.
Along that actual slice morphism between the representing schemes, the
pullback of `L`'s universal line bundle is isomorphic to the universal
line bundle of `L.reindex φ`. The construction is
`universalPullbackIso` followed by the equality transport from the inverse
law of the representing bijection.

For two supplied representations `e` and `d` of the same `F`,
`homEquiv_uniqueUpToIso` verifies that Mathlib's canonical
`e.uniqueUpToIso d` classifies the universal family of `e` using the
representation `d`. `universalCompareIso` consequently identifies the
pullback of `L.universal d` along this actual representing isomorphism
with `L.universal e`. Its proof evaluates `universalPullbackIso` at that
morphism and transports the classified family by the verified equality.

This is internal derived content from the published coherent
`PresheafLineBundle` interface and Mathlib's natural representing
bijections and Yoneda uniqueness construction. It supplies actual
isomorphisms of line bundles, with no choice of extra trivializations.
Representations are explicit inputs; no representability, ampleness or
effective descent theorem is asserted.
