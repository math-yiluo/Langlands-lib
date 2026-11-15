# The descent datum on a saturated open of `X'`

Module `Langlands.AlgebraicGeometry.UnramifiedFunctor.CompletionDescent.ChartDatum`,
namespace `Langlands.AlgebraicGeometry.UnramifiedFunctor.CompletionDescent`.

This is a helper module for the proof of Step 2b of Murre's induction
(`MurreCompletionDescentProof.md`). Its definitions are internal to that proof and
are not meant to match a literature definition.

Setting: `π : S' ⟶ S`, a presheaf `F` on `Over S`,
`e : (baseChange π F).RepresentableBy (Over.mk q')` for `q' : X' ⟶ S'`, and
`σ : X' ×_S S' ⟶ X'` with `hσ : σ ≫ q' = snd`. The hypothesis
`hσpt : pt σ = pt fst` says that `σ` and the first projection have the same element of
`F(X' ×_S S')` (see `exists_sigma` in `Points.md`). Let `j : W ⟶ X'` be an open
immersion that is *saturated*:
`hsat : ∀ z, fst z ∈ range j → σ z ∈ range j`.

## Definitions

- `chartPullMap j : W ×_S S' ⟶ X' ×_S S'`, the map `j × id`, i.e.
  `pullback.lift (fst ≫ j) snd`. Its projections are recorded in
  `chartPullMap_fst` and `chartPullMap_snd`.
- `chartSigma j hsat : W ×_S S' ⟶ W`, the restricted descent datum. It is the lift
  through the open immersion `j` of `chartPullMap j ≫ σ`, whose range lies in
  `range j` by saturation (`range_chartPullMap_sigma`). `chartSigma_j` is the
  factorization `chartSigma ≫ j = chartPullMap ≫ σ`.

## Results

- `sigma_comp_eq`: `σ ≫ q' ≫ π` is the structure morphism of `prodOver q' π`.
- `pt_sigma`: `hσpt` holds after every base change `κ : T ⟶ X' ×_S S'`, i.e.
  `pt (κ ≫ σ) = pt (κ ≫ fst)`. This is `pt_comp` along `κ`.
- `chartSigma_comp`: `chartSigma ≫ j ≫ q' = snd`.
- `chart_fst_comp`: the pullback condition for `W ×_S S'`.
- `pt_chartSigma`: for every `κ : T ⟶ W ×_S S'`,
  `pt (κ ≫ chartSigma ≫ j) = pt (κ ≫ fst ≫ j)`. This is `pt_sigma` applied to
  `κ ≫ chartPullMap j`.
- `chartSigma_section`: the graph `δ := pullback.lift (𝟙 W) (j ≫ q')` is a section,
  `δ ≫ chartSigma = 𝟙 W`. Proof: after composing with the monomorphism `j`, both
  `δ ≫ chartSigma ≫ j` and `j` lie over `j ≫ q'` and have the same element of `F` by
  `pt_chartSigma`. So `pt_inj` applies.
- `chartSigma_cocycle`: the cocycle identity
  `firstLift ≫ chartSigma = secondLift ≫ chartSigma` on `(W ×_S S') ×_S S'`, with
  `firstLift` and `secondLift` from `QuasiAffine.md`. Proof: again compose with `j`.
  Both sides lie over the last projection. Three applications of `pt_chartSigma`
  (to `firstLift`, to `secondLift` and to the first projection of the triple
  product) show that both sides have the same element of `F` as the first factor.
  Then `pt_inj` applies.
- `exists_chart_isPullback`: if `S`, `S'` are affine, `π` is flat and surjective, and
  `W` is quasi-affine, then there are `V`, `w : V ⟶ S` and `p : W ⟶ V` with
  `IsPullback p (j ≫ q') w π` and `fst ≫ p = chartSigma ≫ p`. This is
  `exists_isPullback_of_isQuasiAffine` (`QuasiAffine.md`) applied to
  `g := j ≫ q'` and the descent datum `chartSigma`, using `chartSigma_comp`,
  `chartSigma_section` and `chartSigma_cocycle`.
