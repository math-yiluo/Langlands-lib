# Hom presheaves and explicit morphism-universe lifts

For any category-valued pseudofunctor `F` on the opposite of a category
`C`, `PseudofunctorHomLift.presheafHomIso F M N` identifies the Hom
presheaf of its explicit morphism-universe lift with
`F.presheafHom M N ⋙ uliftFunctor`. The objects `M` and `N` lie over
the same base object. The comparison is natural on the entire slice
over that base, with independent base, fibre-object, fibre-morphism
and lift universes. No groupoid hypothesis is needed.

The components are identity isomorphisms of types: an arrow in
`ULiftHom` is already the explicit `ULift` of an original arrow.
The public lemma `pullHom_down` proves the required compatibility
with coherent pullback. After substituting the two specified composite
base arrows, it unfolds `pullHom` and the pseudofunctor composition
comparison, reducing the equality to reflexivity. Naturality of
`presheafHomIso` follows by lowering the lifted arrow and applying
that lemma to each arbitrary slice morphism.

This is an internal extraction of Worker 214's generic private lemmas
`lifted_pullHom_down` and `presheafHomLiftIso` in
`CoherentSheaves.IsomPresheaf`. Worker 149 exposes the same argument
in the generic sites namespace for reuse by the actual Picard
pseudofunctor. The original coherent-family module is unchanged.
The only mathematical inputs are the published `homLift` construction
and Mathlib's actual `Pseudofunctor.presheafHom` and coherent
`pullHom`. This pair constructs a comparison of presheaves and
does not assert representability or atlas existence.
