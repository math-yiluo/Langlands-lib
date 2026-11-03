# Base change of affine finitely presented presheaf representations

This internal construction restricts a representation on the full slice over a
scheme `B` along any morphism `g : T ⟶ B`. The presheaf convention and the
explicit lift of its values are those of `AlgebraicSpace.Presheaf` and
`schemeYoneda`.

`affineRepresentationBaseChange` takes an actual representative `I : Over B`,
a natural isomorphism from its functor of points to `F`, and affineness and local
finite presentation of `I.hom`. It returns the natural comparison for the actual
object `(Over.pullback g).obj I`, together with both properties of its structure
map. The natural comparison is the published `representedBaseChangeIso`,
which uses the map–pullback adjunction on the entire slice. The structure map
is `pullback.snd I.hom g`; both properties follow from Mathlib's stability under
base change. There is no restriction on `g` or on test schemes.

`IsAffineFinitePresentationRepresentable.baseChange` applies this construction
to a witness of the published representability predicate. It proves that
`(Over.map g).op ⋙ F` has an actual affine locally finitely presented scheme
representative. This formal preservation result uses the existing representation
and does not establish geometric representability of a new presheaf.

The provenance is derived: the construction combines the published scheme
base-change comparison with Mathlib's ordinary affine and local
finite-presentation base-change instances.
