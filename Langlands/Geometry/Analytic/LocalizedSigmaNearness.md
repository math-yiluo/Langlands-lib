# Test relations on disjoint unions of analytic spaces

This is a helper module of `InducedSpaceContinuityProof`. It proves facts
about Berkovich's test relations (Library `StrongNear` and `IsNear`, module
`ContinuousAnalyticAction`) for disjoint unions of analytic spaces. The facts
cover maps that miss the test domain, the position of test domains in a
disjoint union, and gluing the test relation over the summands. Everything is
stated for an arbitrary family, not only for the copies of an induced space.
The content is internal: no literature source states these lemmas. They are the
formal counterparts of the observation that a disjoint union is tested summand
by summand.

## Maps missing the test locus

- `strongNear_of_preimage_eq_empty`: let `a b : T ⟶ B` be strong maps (of
  `SaturatedAtlasPresentation.{u, v, v} K`) and `τ` a test triple on `B`. If
  `a⁻¹(τ.locus)` and `b⁻¹(τ.locus)` are both empty, then `StrongNear τ a b`.
  Both preimages are empty, hence equal, and the covering condition is vacuous. A test
  piece (a chart of `T` whose image under `a` lies in `τ.locus`) would contain
  a point of `a⁻¹(τ.locus)`, so the bound condition is vacuous too.
- `isNear_of_preimage_eq_empty`: let `φ ψ : Y ⟶ X` be morphisms of the
  localized category whose underlying continuous maps (`localizedSpaceFunctor`)
  both miss `τ.locus`. Then `IsNear τ φ ψ`. Proof:
  `exists_commonStrongNumerators` writes `map s ≫ φ = map a` and
  `map s ≫ ψ = map b` with a common quasi-isomorphism `s`. By
  `numerator_point_eq_of_fraction_equation`, `φ (s x) = a x` and
  `ψ (s x) = b x`, so `a` and `b` miss `τ.locus`. The previous lemma and
  `isNear_iff_numerators` conclude.

## Charts of chosen disjoint unions

Let `S : J → SaturatedAtlasPresentation.{u, max z v, max z v} K`. The point
`(sigmaCofan S).pt` is `sigmaPresentation S`, the saturation of the disjoint
union of the nonempty-chart presentations of the `S j`. Its space is
`(j : J) × (S j).presentation.space` (Library `sigmaPresentation_space`).

- `sigmaCofan_inj_baseMap_apply`: the base map of the `j`-th inclusion is
  `x ↦ ⟨j, x⟩` (definitional).
- `exists_sigma_chart_eq_image`: a chart `i` of `nonemptyReplacement (S j)` is
  a local domain `D` of the nonempty-chart atlas of `S j`. Then `D` is also a
  local domain at the index `⟨j, D.index⟩` of the disjoint-union atlas. This
  gives a chart `k` of the disjoint union whose range is the image of the range
  of `i` under the `j`-th inclusion.
- `TestTriple.exists_locus_subset_range_sigmaMk`: for every test triple `τ` of
  `(sigmaCofan S).pt` there is one `j` with
  `τ.locus ⊆ Set.range (Sigma.mk j)`. The domain of `τ` is a saturated chart,
  i.e. a local domain inside a single chart of the disjoint-union atlas, and
  every chart of that atlas lies in one summand.
- `StrongNear.of_sigma` (gluing of the strong relation): let
  `a b : (sigmaCofan S).pt ⟶ B` be strong maps with
  `StrongNear τ ((sigmaCofan S).inj j ≫ a) ((sigmaCofan S).inj j ≫ b)` for
  every `j`. Then `StrongNear τ a b`.
  - Preimages: they are compared at each point `⟨j, x⟩`.
  - Covering: a test piece of the `j`-th composites gives a chart of the sum
    by `exists_sigma_chart_eq_image`, and that chart is a test piece for
    `a, b`.
  - Bound: let `k` be a test piece of the sum and `p` a point of its spectrum.
    Write `chart k p = ⟨j, x⟩`. Take a chart of the summand containing `x`
    (`exists_chart_mem`). By `exists_subchart_image_subset`, a subchart `k'`
    is mapped by the `j`-th inclusion into `k` and still contains `x`. Then `p`
    is the image of a point `p'` of the spectrum of `k'`, by injectivity of
    `chart k` and `chart_comm`. `k'` is a test piece of the composites.
    `comp_pullback_eq` writes the pullbacks of the test function along the
    composites as pullbacks along the inclusion. The bound for the `j`-th
    summand at `p'` is the required bound at `p`.

## Gluing in the localized category

Let `Xf : J → LocalizedCategory.{u, max z v, max z v} (K := K)` and
`F j = presentationOf (Xf j)`. The inclusions of `localizedSigmaCofan Xf` are
built from `(sigmaCofan F).inj j` and the quasi-isomorphisms
`nonemptyReplacementHom (F j)`.

- `localizationFunctor_map_nonemptyReplacementHom_comp_localizedSigmaCofan_inj`:
  `map (nonemptyReplacementHom (F j)) ≫ (localizedSigmaCofan Xf).inj j =
  map ((sigmaCofan F).inj j)`.
- `isNear_of_localizedSigmaCofan` (gluing of the test relation): let
  `φ ψ : (localizedSigmaCofan Xf).pt ⟶ Z` and let `τ` be a test triple on
  `Z`. If `IsNear τ (inj j ≫ φ) (inj j ≫ ψ)` for every `j`, then
  `IsNear τ φ ψ`. Proof:
  1. Precompose with `map (nonemptyReplacementHom (F j))` (`IsNear.precomp`)
     and use the previous identity.
  2. `isNear_iff_numerators` gives, for each `j`, a quasi-isomorphism
     `s j : T j ⟶ nonemptyReplacement (F j)` and strongly near numerators
     `a j, b j`.
  3. Glue on the disjoint union of the `T j`. The denominator is the
     descended map of
     `(nonemptyReplacementHom (T j) ≫ s j) ≫ (sigmaCofan F).inj j`, a
     quasi-isomorphism by `isQuasiIso_sigmaCofan_desc`. The numerators are
     the descended maps of `nonemptyReplacementHom (T j) ≫ a j` and
     `nonemptyReplacementHom (T j) ≫ b j`.
  4. The fraction equations hold on each summand, so they hold by the
     uniqueness part of the localized coproduct
     (`(rightFractionCoproducts K J).hom_ext`).
  5. The glued numerators are strongly near by `StrongNear.precomp` on each
     summand and `StrongNear.of_sigma`. `isNear_iff_numerators` concludes.
- `localizedSpaceFunctor_map_localizedSigmaCofan_inj`: the underlying
  continuous map of `(localizedSigmaCofan Xf).inj j` is `x ↦ ⟨j, x⟩`, by
  `numerator_point_eq_of_fraction_equation`.
- `TestTriple.exists_locus_subset_range_localizedSigmaCofan`: every test triple
  of `(localizedSigmaCofan Xf).pt` has its locus inside one summand
  `Set.range (Sigma.mk j)`.
- `isCompact_preimage_localizedSigmaCofan_inj`: the preimage of `τ.locus`
  under the `j`-th inclusion is compact. `Sigma.mk j` is a closed embedding and
  `τ.locus` is compact (`TestTriple.isCompact_locus`).
- `preimage_locus_comp_localizedSigmaCofan_inj_eq_empty`: let
  `τ.locus ⊆ Set.range (Sigma.mk j₀)` and `j ≠ j₀`. Then for every
  `f : W ⟶ Xf j`, the underlying map of `f ≫ inj j` misses `τ.locus`.
