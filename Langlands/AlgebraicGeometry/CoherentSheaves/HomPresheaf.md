# Actual Hom presheaves of coherent families

`FamilyGroupoid.homPresheaf f M N` retains all maps of the ordinary
pullbacks of the underlying module sheaves. It is defined on the entire
slice `Over T.left`, with values explicitly lifted to `Type (u + 1)`.
It uses the published `Family.pseudofunctor`, before passage to its core,
and Mathlib's coherent `Pseudofunctor.presheafHom`, followed by the
iterated-slice functor.

`homPointsEquiv` identifies its sections with actual module maps.
The inverse wraps a map in the full family subcategory and then in the
universe lift. `homIdentity` and `homCompose` are the actual identity
and composition. Their restriction laws are first proved for an arbitrary Cat-valued
pseudofunctor, then specialized to coherent families. In coherent
pullback: the middle inverse/comparison maps cancel, and ordinary
pullback preserves identities and composition.

This is the scheme-family specialization of the Hom functor defined
in Situation 99.3.1 and equation 99.3.1.1 of the Stacks Project,
Section 99.3 (Tag 08JS). The retained original is `08JS.html` in
registered source `stacks-hom-functor-08js-2026-11-02`, folder SHA-256
`2d60cda5ae13d9daa5c318ca4cd199e47a3a00b39f5062492b2207f7b56432c4`.
The section and proofs were read in full. Its two comments concern a
corrected parenthesis in a displayed formula. No project errata note was
found in the supplied public tree.

No properness assumption is needed for this construction. This module
asserts no sheaf condition or geometric representability.
