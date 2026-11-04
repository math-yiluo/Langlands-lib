# The actual algebra tail after an initial ring stage

This internal construction supplies the initial-stage tail used in Brian
Conrad, *Weil and Grothendieck approaches to adelic points* (December 31,
2011), printed pp. 5–6, Theorem 3.4. Conrad starts with a directed system
of rings, chooses an initial stage, and then considers all later stages
as algebras over that ring. The construction here permits a small filtered
category and arbitrary, possibly noninjective, transition maps.

For an actual functor `F : J ⥤ CommRingCat` and an object `j₀`, the tail
index is the actual category `Under j₀`. Its objects are arrows
`j₀ → j`, and its morphisms are commuting triangles. For a directed
poset this is exactly the usual tail of indices `j ≥ j₀`. The algebra
functor `initialRingAlgebraDiagram F j₀` is `Under.post F` followed by
Mathlib's inverse equivalence from rings under `F.obj j₀` to commutative
`F.obj j₀`-algebras. The displayed formulas prove that its ring at an
arrow is literally `F.obj j`, that its algebra map is the image of the
arrow, and that its transition ring maps are the original `F.map` maps.
All sizes share an arbitrary universe `u`.

For any actual ring cocone `c`, `initialRingAlgebraCocone` is its
`underPost` cocone transported by that same equivalence. Its underlying
ring is literally `c.pt`, with algebra structure given by `c.ι.app j₀`.
Each cocone algebra map has underlying ring map `c.ι.app j.right`.
These are definitional comparisons, not unspecified isomorphisms.

When `J` is filtered, Mathlib makes `Under j₀` filtered and its forgetful
functor final. From an actual `IsColimit c` witness,
`initialRingAlgebraCoconeIsColimit` uses `IsColimit.underPost` to prove
that the tail cocone is colimiting in rings under the initial ring,
then uses preservation by the equivalence to prove the algebra-colimit
universal property. Thus the original colimit ring, with its specified
initial-stage algebra structure, is proved to be the actual tail
colimit. This property is a constructed witness, not a new assumption.

The last three equations connect this tail to the published actual
spectrum construction. Its structural maps are `Spec.map (F.map j.hom)`,
its limiting structural map is exactly `Spec.map (c.ι.app j₀)`, and its
cone legs are `Spec.map (c.ι.app j.right)`. Consequently
`spectrumConeIsLimit` applies using the constructed tail algebra-colimit
witness. These comparisons permit the fixed-base model interfaces to
use the initial stage in the original ring system, including arbitrary
nonaffine models.

This file constructs the tail, its universal property, and the spectrum
identifications. The relative Hom comparison, property descent and their
source-qualified consequences are separate assertions. It does not add
any arithmetic or topological hypotheses or claim those consequences.
