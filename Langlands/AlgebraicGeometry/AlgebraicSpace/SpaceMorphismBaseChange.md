# Morphism properties under scheme base change

This is internal infrastructure for property descent of algebraic-space morphisms.
It uses the existing restriction construction and categorical pullback preservation;
there is no additional geometric hypothesis and no assertion of limit descent.

`restrictPresheafPullbackIso` compares the restriction of the actual presheaf
pullback with the pullback of the restricted maps. It is Mathlib's canonical
comparison for a functor preserving pullbacks. The comparison carries a relative
diagonal to the relative diagonal, so any represented scheme property of that
diagonal which respects isomorphisms is preserved by restriction.

`schemeYonedaBaseChangeNatIso` packages the existing scheme representation
comparisons into a natural isomorphism in the represented scheme. Naturality is
the right naturality of the adjunction between composition and pullback in the
slice category. `restrictAtlas_square` uses that naturality to restrict an entire
commutative chart square.

The final lemmas preserve closed immersion, open immersion, finite and affine
morphism predicates under arbitrary scheme base change, using the published
`relative_restrictPresheaf_map`. Separatedness follows by applying the same
argument to the relative diagonal. Local finite type and smoothness are preserved
by restricting the witnessing chart square, using its base-changed scheme
morphism. `schemeProperty_overPullback_map` establishes the latter preservation
for any scheme property stable under base change, by cancelling the target
pullback square from the source pullback square. These are preservation
statements only; properness and connected fibres are not asserted in this unit.

The constructions and proofs are derived directly from the imported definitions;
no outside literature is used for this internal comparison unit.
