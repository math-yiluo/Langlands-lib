# Fibre products of algebraic spaces with schemes

Author: Worker 78.

For a morphism of algebraic spaces `f : X ⟶ Y` over a scheme `S` and a map
`g : h_V ⟶ Y` from the functor of points of an actual scheme `V` over `S`, this module
constructs the fibre product `X ×_Y h_V` as an algebraic space when `f` is separated and
quasi-compact and `V` is affine and separated over `S`. Over an affine base `Spec C`, with
`X` locally of finite type and `g` étale, the fibre product is of finite type over `C`.
The construction is auxiliary, with internal provenance; it is the special case needed here of
the Stacks Project fact that fibre products of algebraic spaces are algebraic spaces
(*Spaces*, Lemma 65.7.3), and of the stability of separatedness under base change and
composition.

## Definitions

- `ChartFibre.fibre f g` for presheaf maps `f : F ⟶ G`, `g : H ⟶ G`: the elementwise fibre
  product, whose sections over `T` are pairs `(x, h) ∈ F(T) × H(T)` with `f x = g h`;
  `ChartFibre.fst`, `ChartFibre.snd` are the projections, and `ChartFibre.isPullback` shows
  that the square is a pullback of presheaves.
- `ChartFibre.space f g hf hqc` is the algebraic space with underlying presheaf
  `fibre (hom f) g`; `ChartFibre.pr₁` and `ChartFibre.pr₂` are the projections to `X` and to
  the space of `V`. Its rational points are literally pairs of a point of `X` and a point of
  `V` with the same image in `Y`.

## Results and proofs

- `yoneda_symm_comp`, `yoneda_symm_map`: the Yoneda lemma for presheaves with values in
  `Type (u + 1)`, with the universe fixed.
- `exists_representsEqualizer_of_isSeparatedMorphism`: for separated `f`, two sections of `X`
  over `U` with the same image in `Y` agree exactly on a closed subscheme of `U`. The closed
  subscheme is the represented pullback of the relative diagonal `X ⟶ X ×_Y X`
  (`IsSeparatedMorphism`) along the pair of sections; the equalizer property is checked as in
  the Library's `exists_representsEqualizer_of_relative_diag`.
- `isSheaf_fibre`: the fibre product of fppf sheaves is a sheaf (sheaves are closed under
  limits in presheaves).
- `exists_representsEqualizer_fibre`, `isClosedImmersion_diag_fibre`: for two sections
  `(x₁, v₁)`, `(x₂, v₂)` over `U`, first take the closed subscheme `Z₁ ⊆ U` where `v₁ = v₂`
  (diagonal of the separated scheme `V`); there `f x₁ = f x₂`, and the previous result gives
  the closed subscheme `Z₂ ⊆ Z₁` where also `x₁ = x₂`. The composite closed immersion
  `Z₂ ⟶ U` represents the equalizer, so by the Library's
  `isClosedImmersion_diag_of_representsEqualizer` the diagonal is a closed immersion.
- `exists_atlas_fibre`: `IsQuasiCompactMorphism f` applied to the affine `V` gives an étale
  surjective atlas of `Limits.pullback (hom f) g` from a quasi-compact scheme, transported to
  the elementwise fibre product.
- `isAlgebraicSpace_fibre`, `space`, `isSeparated_space`: the diagonal is representable since
  it is a representable closed immersion, so the fibre product is a separated algebraic space.
- `isEtale_fst`: the first projection is étale when `g` is (base change of a representable
  étale map).
- `finiteTypeOverRing_space`: the quasi-compact atlas `U` is locally of finite type over
  `Spec C` by the Library's `locallyOfFiniteType_of_isEtale` applied to the étale composite
  `h_U ⟶ X ×_Y h_V ⟶ X`, and quasi-compact over the affine `Spec C` since `U` is compact.
