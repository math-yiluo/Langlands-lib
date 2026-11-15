# The element of `F` carried by a descended chart

Module `Langlands.AlgebraicGeometry.UnramifiedFunctor.CompletionDescent.ChartProperties`,
namespace `Langlands.AlgebraicGeometry.UnramifiedFunctor.CompletionDescent`.

This is a helper module for the proof of Step 2b of Murre's induction
(`MurreCompletionDescentProof.md`). Its definitions are internal to that proof and
are not meant to match a literature definition. `FaithfullyFlatSheaf` (condition
(F1b)), `IsMonoElement` and `InfinitesimallyEtaleAt` are the published notions from
`MurreCriterionStatement` and `MurreLocalToGlobalSteps`.

## Base change of test objects (section `Base`)

For `π : S' ⟶ S` and `T : Over S`:

- `pullOver π T : Over S` is `T ×_S S'`, with structure morphism `snd ≫ π`.
- `pullHom π T : pullOver π T ⟶ T` is the first projection. `pullHom_left` gives its
  underlying morphism.
- `flat_pullHom`, `surjective_pullHom`, `quasiCompact_pullHom`: the first projection
  inherits flatness, surjectivity and quasi-compactness from `π`, by base change
  (`MorphismProperty.of_isPullback`).
- `injective_map_pullHom`: if `F` satisfies `FaithfullyFlatSheaf` and `π` is flat,
  surjective and quasi-compact, then `F.map (pullHom π T).op` is injective. This is
  the separatedness part of the sheaf condition for the singleton presieve.

`map_map` is functoriality, `F.map f.op (F.map g.op x) = F.map (f ≫ g).op x`.

## Charts

Setting: the notation of `ChartDatum.md` (`e`, `σ`, `hσ`, `hσpt`, a saturated open
immersion `j : W ⟶ X'` with `hsat`). In addition, `hpb : IsPullback p (j ≫ q') w π`
for `p : W ⟶ V`, `w : V ⟶ S`, and `hfst : fst ≫ p = chartSigma j hsat ≫ p`. These
are the outputs of `exists_chart_isPullback`.

Definitions:

- `chartOver j q' π : Over S` is `W` with structure morphism `(j ≫ q') ≫ π`.
- `chartHom j hpb : chartOver j q' π ⟶ Over.mk w` is `p`.
- `IsChartElement e j hpb ξ` for `ξ ∈ F(V)` is the proposition
  `F.map (chartHom j hpb).op ξ = pt e (chartOver j q' π) j _`: `ξ` pulls back along
  `p` to the element of `F(W)` defined by `j`.

Results:

- `comp_p_w`: if `k ≫ j ≫ q' ≫ π = T.hom`, then `(k ≫ p) ≫ w = T.hom`.
- `pt_comp_chart`: if `IsChartElement e j hpb ξ`, then for `k : T.left ⟶ W` over `S`,
  `pt (k ≫ j) = F.map (k ≫ p) ξ`. This follows by factoring `k ≫ p` through `chartHom`
  and applying `pt_comp`.
- `comp_p_eq_of_pt_eq`: if `a, b : T.left ⟶ W` over `S` have
  `pt (a ≫ j) = pt (b ≫ j)`, then `a ≫ p = b ≫ p`. Proof: let
  `κ := (a, b ≫ j ≫ q') : T ⟶ W ×_S S'`. By `pt_chartSigma` and `pt_inj`,
  `κ ≫ chartSigma = b`. Then `a ≫ p = κ ≫ fst ≫ p = κ ≫ chartSigma ≫ p = b ≫ p` by
  `hfst`.
- `pt_eq_of_comp_p_eq`: the converse. If `a ≫ p = b ≫ p`, then `κ ≫ chartSigma = b`
  holds by the uniqueness part of the pullback `hpb` (using `hfst` and
  `chartSigma_comp`). Hence `pt (a ≫ j) = pt (b ≫ j)` by `pt_chartSigma`.
- `exists_isChartElement`: if `F` satisfies `FaithfullyFlatSheaf` and `π` is flat,
  surjective and quasi-compact, then some `ξ ∈ F(V)` satisfies `IsChartElement`. Proof:
  `p` is flat, surjective and quasi-compact, being a base change of `π` (via `hpb`).
  So `F` is a sheaf for the singleton presieve on `chartHom`. The element `pt j` is
  compatible: for `p₁, p₂ : Z ⟶ W` with `p₁ ≫ p = p₂ ≫ p`, `pt_comp` and
  `pt_eq_of_comp_p_eq` give `pt (p₁ ≫ j) = pt (p₂ ≫ j)`. The amalgamation is `ξ`.
- `chartLift j hpb h : T ×_S S' ⟶ W`, for `h : T ⟶ Over.mk w`, is the morphism given by
  `hpb` from `fst ≫ h.left` and `snd`. `chartLift_p`, `chartLift_q`, `chartLift_comp`
  record its composites. `pt_chartLift` says that `pt (chartLift h ≫ j)` is the
  pullback of `F.map h.op ξ` to `T ×_S S'`.
- `isMonoElement_of_isChartElement`: if `π` is flat and surjective, then `ξ` is a
  monomorphism. Proof: if `F.map h₁.op ξ = F.map h₂.op ξ`, then `pt_chartLift` and
  `pt_inj` give `chartLift h₁ ≫ j = chartLift h₂ ≫ j`, hence `chartLift h₁ = chartLift h₂`
  (`j` is a monomorphism). Composing with `p` gives `fst ≫ h₁.left = fst ≫ h₂.left`.
  The flat surjection `fst : T ×_S S' ⟶ T` is an epimorphism
  (`Flat.epi_of_flat_of_surjective`).
- `exists_map_eq_of_range_subset`: let `v ∈ F(T)`, and let `v' : T ×_S S' ⟶ X'` lie
  over `snd` with `pt v' = F.map (pullHom π T).op v` (it exists by `exists_pt`). If
  `range v' ⊆ range j`, then there is `h : T ⟶ Over.mk w` with `F.map h.op ξ = v`.
  Proof: lift `v'` through `j` to `v''`. The morphism `v'' ≫ p` coequalizes every pair
  `g₁, g₂ : Z ⟶ T ×_S S'` with `g₁ ≫ fst = g₂ ≫ fst`, because both `pt (gᵢ ≫ v'' ≫ j)`
  are the pullback of `v` along the same morphism `Z ⟶ T`; this uses
  `comp_p_eq_of_pt_eq`. The flat surjective quasi-compact morphism `fst` is an
  effective epimorphism (Mathlib's fpqc results), so `v'' ≫ p` descends to
  `u₀ : T.left ⟶ V`, which lies over `S`. Finally `F.map u₀ ξ = v` holds after
  applying the injective map `F.map (pullHom π T).op` (`injective_map_pullHom`), by
  `pt_comp_chart`.
- `range_subset_of_map_eq`: a converse used for infinitesimal étaleness. Let
  `b : T₀ ⟶ T` be surjective on points and `u₀ : T₀ ⟶ Over.mk w` with
  `F.map u₀.op ξ = F.map b.op v`. Then `range v' ⊆ range j`. Proof: on
  `Q := T₀ ×_T (T ×_S S')`, the pullback `hpb` gives `k₀ : Q ⟶ W` over `u₀` and `snd`.
  By `pt_comp_chart`, the hypothesis and `hv'`, the morphisms `k₀ ≫ j` and
  `snd ≫ v'` have the same element of `F(Q)` and lie over the same morphism to `S'`,
  so they are equal (`pt_inj`). The projection `Q ⟶ T ×_S S'` is surjective, being a
  base change of `b`.
- `infinitesimallyEtaleAt_of_isChartElement`: under the hypotheses of
  `exists_isChartElement`, `ξ` is infinitesimally étale at every point of `V`. Proof:
  let `A` be local artinian, `J` nilpotent, `u₀ : Spec(A/J) ⟶ V` and
  `v ∈ F(Spec A)` with `ξ ∘ u₀ = v|_{Spec(A/J)}`. The closed immersion
  `Spec(A/J) ⟶ Spec A` is bijective on points, since `J` lies in the nilradical
  (`PrimeSpectrum.comap_quotientMk_bijective_of_le_nilradical`). By
  `range_subset_of_map_eq` and `exists_map_eq_of_range_subset`, `v` factors as
  `F.map h.op ξ`. The identity `algebraOverBase ≫ h = u₀` and uniqueness both follow
  from `isMonoElement_of_isChartElement`. The condition on the image point of `u₀` is
  not used.
- `locallyOfFiniteType_w`: if `q'` is locally of finite type and `π` is flat,
  surjective and quasi-compact, then `w` is locally of finite type. Its base change
  `j ≫ q'` along `π` is locally of finite type, and this property descends along such
  morphisms (Mathlib instance from `LocalFlatDescent`,
  `MorphismProperty.of_isPullback_of_descendsAlong`).
