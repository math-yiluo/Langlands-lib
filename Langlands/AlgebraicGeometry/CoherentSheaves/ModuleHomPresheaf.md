# Forgetting family conditions in the actual Hom presheaf

This internal comparison removes the full-subcategory wrappers from the
published coherent-family Hom presheaf. It does not assert representability.

`moduleHomPresheaf f M N` is the presheaf of all maps between ordinary
pullbacks of two actual module sheaves on `T.left ×_S X`. It has the same
full slice `Over T.left` and explicit `ULift` as `FamilyGroupoid.homPresheaf`.
No finiteness or flatness condition is needed to define it.
`moduleHomPointsEquiv` is the identity identification with actual module
maps on the published relative-space pullbacks.

`fullsubcategoryPresheafHomIso` works for any Cat-valued pseudofunctor and
any property preserved by its restriction functors. Its components forget
or insert the full-subcategory morphism wrapper. The proof of naturality
checks `pullHom`: after substituting the composite arrows, the comparison
maps, pulled-back map and their composites have exactly the original
underlying morphisms.

`FamilyGroupoid.homPresheafModuleIso` specializes this comparison to the
published family property, then reindexes by the iterated-slice functor
and applies the universe lift. Its two component formulas show that it
retains every actual module map. Naturality includes every morphism of
test schemes and the original ordinary-pullback coherence maps.

The provenance is the published `HomPresheaf` construction and Mathlib's
full-subcategory pseudofunctor. It realizes the passage from actual family
objects to the underlying modules in Stacks Project Situation 99.3.1 and
formula 99.3.1.1 (Tag 08JS). The retained original is `08JS.html` in
registered source `stacks-hom-functor-08js-2026-11-02`, folder SHA-256
`2d60cda5ae13d9daa5c318ca4cd199e47a3a00b39f5062492b2207f7b56432c4`.
The whole section and proofs were read; its two comments concern a
corrected displayed-formula parenthesis. No project errata entry was found.
This is a derived categorical comparison, not a separate theorem claimed
in that source, and does not prove its geometric Hom representability.
