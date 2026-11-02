# Presheaves represented by affine finitely presented schemes

`IsAffineFinitePresentationRepresentable F` is a predicate on presheaves `F`
on the full slice `Over B` of schemes over `B`, with values in
`Type (u + 1)`. It holds when `F` is naturally isomorphic to
`(schemeYoneda B).obj I` for some scheme `I` over `B` whose structure
morphism is affine and locally of finite presentation. Here `schemeYoneda B`
is the Library's lifted functor of points. This is exactly the conclusion
shape of the Library statements `ProperHomRepresentabilityStatement` and
`ProperIsomRepresentabilityStatement`. An affine morphism is quasi-compact and
separated, so the two conditions together amount to affine finite
presentation.

## Results

- `of_iso`: the predicate is invariant under natural isomorphism of
  presheaves.
- `prod_hom`: if `I` and `J` are affine and locally of finite presentation
  over `B`, so is their binary product `I ⨯ J` in `Over B`. The proof writes
  `(I ⨯ J).hom` as Mathlib's comparison `Over.prodLeftIsoPullback I J`,
  followed by the first projection of the fibre product `I ×_B J` and then
  `I.hom`. Both properties are stable under base change and composition.
- `of_isLimit_binaryFan`: the point of any limit binary fan of two
  representable presheaves is representable, by the product in `Over B`.
  The functor `schemeYoneda B` preserves the binary product.
- `exists_isLimit_fork`: two morphisms `a b : I ⟶ E` in `Over B`, with `E`
  affine and locally of finite presentation over `B`, have a limit fork in
  `Over B`. Its point `Z` maps to `I` by a closed immersion, and `Z` is affine
  (resp. locally of finite presentation) over `B` whenever `I` is. The proof
  applies the Library theorem
  `AlgebraicGeometry.exists_isClosedImmersion_locallyOfFinitePresentation_iff_comp_eq_of_isSeparated`.
  That theorem is ported from the Anthropic FLT development. It needs `E.hom`
  separated, which follows from affineness. Since `E.hom` is locally of finite
  type, it also yields a closed immersion `j : Z ⟶ I.left` that is locally of
  finite presentation, through which a morphism factors exactly when it
  equalizes `a.left` and `b.left`. A closed immersion is affine, and both
  properties are stable under composition.
- `of_isLimit_fork`: the point of any limit fork of two maps `a b : F ⟶ G`
  between representable presheaves is representable. The maps are transported
  through the representing isomorphisms and pulled back along the fully
  faithful functor `schemeYoneda B`, giving morphisms `I ⟶ E` in `Over B`.
  `exists_isLimit_fork` gives their equalizer. `schemeYoneda B` preserves
  limits, and `Fork.isLimitOfIsos` transports the image fork back to a limit
  fork of `a` and `b`. The point of any limit fork is then identified with it
  up to isomorphism.

## Provenance

The predicate is internal to the Library and introduced as a name for the
common conclusion of the two statements above. The closure properties are the
standard facts used in the proof of Stacks Project Proposition 99.4.3
(Section 99.4, Tag 08K7). There, a fibre product of spaces affine of finite
presentation over the base is again of this kind, and the identity section of
a separated space is a closed immersion of finite presentation. The retained
original is `08K7.html` in registered source
`stacks-isom-functor-08k7-2026-11-02` (folder SHA-256
`a05b61ba562e7e65dd2b64446e779a6bb67af1846c0a00f4a656d64a2b2c27b5`).
The Lean results are proved for schemes and presheaves on the full slice. They
are phrased with limit cones and forks instead of the source's fibre products
with a section.
