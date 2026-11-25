# The normalization model of a scheme over a DVR

For `X` over `Spec R` (`R` a DVR):

- `source X`: the relative normalization `(genericι X).normalization` of `X` in its generic fibre,
  as a scheme over `Spec R` via `fromNormalization ≫ X.hom`.
- `map X : source X ⟶ X`: the normalization map, `map_left` its underlying morphism.
- `isIso_pullback_snd_fromNormalization`: base change of the normalization map along the generic
  fibre inclusion is an isomorphism. Mathlib's `normalizationPullback` is an isomorphism along the
  smooth (open immersion) map `genericι X`, and the normalization of the isomorphism
  `pullback.snd j j` is an isomorphism.
- `isIso_genericMap_left`, `genericIso`: the morphism `(Over.pullback η).map (map X)` between generic
  fibres is an isomorphism; it equals the above base change up to
  `pullbackRightPullbackFstIso`.
- `generic_eq_of_comp_eq`: two maps `T ⟶ source X` over `Spec R` that agree after composing with
  `map X` agree on the generic fibre of `T` (they factor through the generic fibre of the source,
  where `map X` is an isomorphism).
- `normal_lift`: for `T` flat with normal stalks, composition with `map X` is a bijection
  `(T ⟶ source X) → (T ⟶ X)`. Existence: `normalizationDesc` for `genericι T` with target the
  pullback `T ×_X source X`, composed with the inverse of the isomorphism of
  `isIso_fromNormalization_of_normal`. Uniqueness: `normalization.hom_ext` together with
  `generic_eq_of_comp_eq`.

The lifting argument is the one sketched in the paired Markdown of
`DvrStableNormalizationStatement` and in Conrad's Corollary A.4 (p.29).
