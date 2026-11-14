# From a classifier on affine tests to a universal ideal sheaf on all test schemes

Author: Worker 22, for task `07219dde-fd87-48cf-83be-db16cbb3707c` (Task 5705),
as part of the proof of
`Langlands.AlgebraicGeometry.HilbertSchemeUniversalFamilyStatement`. The
operator's answer to request `98389b48910e54088e0e2b2ba6aaad9c` allows such
prerequisite proofs to stay under Task 5705.

All declarations are in the namespace
`Langlands.AlgebraicGeometry.HilbertSchemeUniversalFamily`. The module proves
general facts and adds no axioms. It defines only the abbreviations `mapX`,
`affineFromSpecCover`, `ClassifierNat`, `ClassifierSurj` and `ClassifierUniv`.

## Setting and main result

Let `A` be a commutative ring, `f : X ⟶ Spec A` and `πH : H ⟶ Spec A`. A
*classifier* is a function `pt` that sends every closed immersion
`ιZ : Z ⟶ X ×_A Spec S'` (for a ring `S'`) whose composite with
`pullback.snd` is flat and locally of finite presentation to a morphism
`Spec S' ⟶ H` over `Spec A` (an element of `SchemeHomOver s πH`). This is the
form of the classifiers in the ported FLT Hilbert scheme theorems. Let
`ι : 𝒵 ⟶ X ×_A H` be a closed immersion. The hypotheses are:

- `ClassifierNat f πH pt`: `pt` is compatible with base change along ring maps
  `S' → S''`. This is the hypothesis `hnat` of the FLT theorems, copied
  verbatim.
- `ClassifierSurj f πH pt`: every morphism `Spec S' ⟶ H` over `Spec A` is the
  value of `pt` on some closed subscheme.
- `ClassifierUniv f πH pt ι`: for every such `ιZ` there is `e : Z ⟶ 𝒵` making
  a pullback square of `ιZ ≫ pullback.snd`, `ι ≫ pullback.snd`, `e` and
  `(pt … ιZ …).1`, compatible with `ιZ`, `ι` and the induced map
  `X ×_A Spec S' ⟶ X ×_A H`. This is the conclusion of the Library theorem
  `AlgebraicGeometry.exists_closedSubscheme_pullback_flat_forall_isPullback_of_forall_spec_point`.
- `ι ≫ pullback.snd f πH` is flat and locally of finite presentation.

**`classification`.** Under these hypotheses, let `W := ι.ker`. For every scheme
`T` and `s : T ⟶ Spec A`:

1. for every `g : T ⟶ H` with `g ≫ πH = s`, the closed subscheme of
   `W.comap (mapX f g hg)` is flat and locally of finite presentation over `T`;
2. for every ideal sheaf `I` on `X ×_A T` whose closed subscheme is flat and
   locally of finite presentation over `T`, there is exactly one `g : T ⟶ H`
   with `g ≫ πH = s` and `W.comap (mapX f g hg) = I`.

`T` is arbitrary: not affine, not quasi-compact and not separated in general.

## Section `Kernel`

- `ker_eq_comap_of_isPullback`: in a pullback square
  `IsPullback ι' e h ι` with `ι` a closed immersion, `ι'.ker = ι.ker.comap h`.
  The left side is the canonical `pullback.fst h ι` up to the isomorphism
  `sq.isoPullback`, kernels do not change under precomposition with an
  isomorphism (`Scheme.Hom.ker_comp_of_isIso`), and Mathlib's
  `IdealSheafData.ker_fst_of_isClosedImmersion` computes the kernel of
  `pullback.fst h ι`.
- `isPullback_comap`: the closed subscheme of `I.comap h` sits in a pullback
  square over `h` and `I.subschemeι`; Mathlib's `IdealSheafData.comapIso`
  identifies it with the pullback.
- `eq_of_comap_eq`: let `mᵢ : Vᵢ ⟶ Y` be open immersions whose ranges cover `Y`.
  If two ideal sheaves on `Y` have equal pullbacks along every `mᵢ`, they are
  equal. The proof applies Mathlib's `IdealSheafData.ext_of_iSup_eq_top` to the
  affine opens `mᵢ(V)` for `V` affine in `Vᵢ`, which cover `Y`. On such an open
  the ideals are compared by `ideal_comap_of_isOpenImmersion`: the ideal of the
  pullback is the preimage of the ideal on `mᵢ(V)` under a ring isomorphism,
  and preimage under a surjective ring map is injective on ideals.

## Section `Families`

For `h : T' ⟶ T` with `h ≫ s = s'`, `mapX f h w : X ×_S T' ⟶ X ×_S T` is
`pullback.map` with `𝟙 X` and `h`; it is the map written `g_X` in the statement.

- `mapX_fst`, `mapX_snd`, `isPullback_mapX` (its square with the two
  projections to `T'` and `T` and `h` is a pullback square, by
  `IsPullback.of_right`), `mapX_comp`, `mapX_congr` (independence of the proof
  `w`) and `comap_mapX_comap_mapX` (pulling back along `mapX` twice is pulling
  back along `mapX` of the composite, by Mathlib's `IdealSheafData.comap_comp`).
- `flat_lfp_comap`: if the closed subscheme of `I` on `X ×_S T` is flat and
  locally of finite presentation over `T`, so is the closed subscheme of
  `I.comap (mapX f h w)` over `T'`. The square of `isPullback_comap` pasted
  with `isPullback_mapX` shows that it is the base change of the former along
  `h`; both properties are stable under base change
  (`MorphismProperty.of_isPullback`).
- `isOpenImmersion_mapX`: for an open immersion `h`, `mapX f h` is an open
  immersion (base change).
- `iSup_opensRange_mapX`: for open immersions `jᵢ : Vᵢ ⟶ T` that are jointly
  surjective, the open immersions `mapX f jᵢ` cover `X ×_S T`. A point `x`
  with `pullback.snd x` in the range of `jᵢ` lies in the range of
  `pullback.fst (pullback.snd f s) jᵢ` (Mathlib `Scheme.Pullback.range_fst`),
  which is the range of `mapX f jᵢ` up to the isomorphism of the pullback square.

## The affine open cover `affineFromSpecCover`

`affineFromSpecCover T` is the open cover of `T` by the morphisms
`U.2.fromSpec : Spec Γ(T, U) ⟶ T` for the affine opens `U` of `T`, built with
`Scheme.Cover.mkOfCovers` from `exists_fromSpec_eq` (every point lies in the
range of some `U.2.fromSpec`, by `iSup_affineOpens_eq_top` and
`IsAffineOpen.range_fromSpec`). The lemma `isOpenImmersion_affineOpens_fromSpec`
is a local instance, because instance search does not recognise `U.2` as a proof
of `IsAffineOpen U`. This cover is used instead of `T.affineCover` because its
pieces are syntactically `Spec` of a ring, so the classifier `pt` applies to
them without unfolding the definition of the cover.

## Section `Classifier`

- `pt_eq_of_iso`: if `e : Z₁ ⟶ Z₂` is an isomorphism with `e ≫ ι₂ = ι₁`, then
  `pt` takes the same value on `ι₁` and `ι₂`. This is `ClassifierNat` for the
  identity of `S'`; `Spec.map (CommRingCat.ofHom (RingHom.id S')) = 𝟙`, the
  induced map on `X ×_A Spec S'` is the identity, and the square is a pullback
  by `IsPullback.of_horiz_isIso`.
- `comap_mapX_pt` (from `ClassifierUniv`): over an affine test, pulling back
  `ι.ker` along `mapX` of the classifying morphism of `ιZ` gives `ιZ.ker`.
  `IsPullback.of_bot` turns the square of `ClassifierUniv` and
  `isPullback_mapX` into a pullback square of `ιZ`, `ι`, `e` and `mapX`; then
  `ker_eq_comap_of_isPullback` applies.
- `eq_pt` (affine uniqueness): if `g : Spec S' ⟶ H` over `Spec A` satisfies
  `ι.ker.comap (mapX f g hg) = I`, then `g` is the classifying morphism of
  `I.subschemeι`. By `ClassifierSurj`, `g` classifies some `ιZ`. By
  `comap_mapX_pt`, `ιZ.ker = I = I.subschemeι.ker`, so `ιZ` and `I.subschemeι`
  are isomorphic over `X ×_A Spec S'` (Mathlib `IsClosedImmersion.isIso_lift`),
  and `pt_eq_of_iso` concludes.
- `flat_lfp_ker`: `ι.ker.subschemeι = inv ι.toImage ≫ ι` (Mathlib
  `Scheme.Hom.toImage_imageι`; `toImage` is an isomorphism for closed
  immersions), so the closed subscheme of `ι.ker` is flat and locally of finite
  presentation over `H` when `𝒵` is.
- `eq_of_comap_eq_comap` (uniqueness on all `T`): two morphisms `g₁, g₂` over
  `Spec A` with the same pulled-back ideal agree after composing with every
  `U.2.fromSpec`. Indeed, both composites pull `ι.ker` back to the same ideal
  `I` (by `comap_mapX_comap_mapX`), `I` is flat and locally finitely presented
  (by `flat_lfp_comap` twice and `flat_lfp_ker`), and `eq_pt` identifies both
  composites with the classifying morphism of `I.subschemeι`. Then
  `Scheme.Cover.hom_ext` on `affineFromSpecCover T` gives `g₁ = g₂`.
- `exists_comap_eq` (existence on all `T`): for each affine open `U`, let
  `g U` be the classifying morphism of the closed subscheme of
  `I.comap (mapX f U.2.fromSpec)` (flat and locally finitely presented by
  `flat_lfp_comap`). By `comap_mapX_pt`, `ι.ker` pulls back along `mapX (g U)`
  to `I.comap (mapX f U.2.fromSpec)`. On the overlap
  `pullback U.2.fromSpec V.2.fromSpec`, which need not be affine, the two
  restrictions of `g U` and `g V` pull `ι.ker` back to the same ideal (the
  pullback of `I`, using `pullback.condition`), so they agree by
  `eq_of_comap_eq_comap`. Mathlib's `Scheme.Cover.glueMorphisms` glues them to
  `G : T ⟶ H`; `G ≫ πH = s` by `Scheme.Cover.hom_ext`. Finally
  `ι.ker.comap (mapX f G _) = I` by `eq_of_comap_eq` for the open immersions
  `mapX f U.2.fromSpec`, which cover `X ×_A T` by `iSup_opensRange_mapX`: both
  sides pull back to `I.comap (mapX f U.2.fromSpec)`, by
  `comap_mapX_comap_mapX` and `Scheme.Cover.ι_glueMorphisms`.
- `classification`: part 1 is `flat_lfp_comap` applied to `ι.ker` (with
  `flat_lfp_ker`); part 2 combines `exists_comap_eq` and
  `eq_of_comap_eq_comap`.

## Source

The argument is the standard extension of a functor from affine tests to all
schemes by Zariski gluing, together with the description of a pulled-back
closed subscheme as a base change. The statement Markdown of
`HilbertSchemeUniversalFamilyStatement` (Derivation, step 3) outlines it. The
universal property is the one used by S. L. Kleiman, *The Picard scheme*
(`kleiman-2005-picard-scheme-arxiv-math0504020v1`), proof of Theorem 3.7, p.24.

## Dependencies

Mathlib (`IdealSheaf.Functorial`, `Morphisms.Flat`,
`Morphisms.FinitePresentation`) and the ported FLT definition module
`Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier`
for `SchemeHomOver`.
