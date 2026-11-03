import Langlands.HarmonicAnalysis.HarishChandraSchwartz.ParabolicHaar
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.CuspidalDecay

/-! # The decomposition of `∫_G f₁(a g a⁻¹) f₂(g) dg` in the proof of Proposition VIII.3.1

Waldspurger 2003, proof of Proposition VIII.3.1 (printed pp. 323–324): with
`S(a) = G - a⁻¹ Γ a M Γ̄`, `∫_G f₁(a g a⁻¹) f₂(g) dg = ∫_{S(a)} … + J(a)`, and by the
open-cell formula of I.1 (2)
`J(a) = γ(G|M)⁻¹ ∫_{a⁻¹Γa × M × Γ̄} f₁(a u m ū a⁻¹) f₂(u m ū) δ_P(m)⁻¹ dū dm du
= γ(G|M)⁻¹ ∫_M φ₁(a, a m a⁻¹) φ₂(a, m) dm`, using the left `Γ`-invariance of `f₁` and the right
`Γ̄`-invariance of `f₂`. This module proves this decomposition for abstract data, in the form
of the hypothesis `hsplit` of `conjugationIntegralBound_of_split`.
-/

noncomputable section

open scoped ENNReal NNReal Pointwise
open MeasureTheory Measure Topology

namespace Langlands.HarishChandraSchwartz

section Split

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G]
  {M U P V : Subgroup G} [SecondCountableTopology U]
  (hMU : M ≤ Subgroup.normalizer (U : Set G)) (hP : ∀ x : M × U, leviUnipotentMul x ∈ P)
  [LocallyCompactSpace P] [LocallyCompactSpace V] [SecondCountableTopology P]
  [SecondCountableTopology V]
  (μ : Measure G) [IsHaarMeasure μ] [μ.IsMulRightInvariant]
  (μM : Measure M) [IsHaarMeasure μM] [SFinite μM]
  (μU : Measure U) [IsHaarMeasure μU] [SFinite μU] (μV : Measure V) [IsHaarMeasure μV]

include hMU in
/-- The open-cell formula for integrable complex functions: `∫_G F dμ = c ∫ F(m u v⁻¹)` over
`(M × U) × V` with `c = μ(K) γ⁻¹`, and `F ∘ openCellCoord` is integrable. -/
theorem integral_eq_smul_integral_openCellCoord (hhomeo : IsHomeomorph (leviUnipotentCoord hP))
    (hι : IsOpenEmbedding (openCellMap (P := P) (V := V)))
    (hnull : μ (Set.range (openCellMap (P := P) (V := V)))ᶜ = 0)
    {K : Subgroup G} (hK : MeasurableSet (K : Set G)) (hK0 : μ K ≠ 0) (hKtop : μ K ≠ ⊤)
    {F : G → ℂ} (hF : Integrable F μ) :
    Integrable (fun x => F (openCellCoord x)) ((μM.prod μU).prod μV) ∧
      ∫ g, F g ∂μ = (μ K * (openCellConstant (leviUnipotentMeasure hP μM μU) μV K)⁻¹).toReal •
        ∫ x, F (openCellCoord x) ∂((μM.prod μU).prod μV) := by
  have heq := eq_smul_map_openCellCoord hMU hP μ μM μU μV hhomeo hι hnull hK hK0 hKtop
  have := leviUnipotentMeasure_isHaarMeasure hMU hP μM μU hhomeo
  obtain ⟨hγ0, hγtop, -⟩ := lintegral_eq_openCellConstant_inv_mul μ
    (leviUnipotentMeasure hP μM μU) μV hι hnull hK hK0 hKtop
  have hφ : Measurable (openCellCoord (M := M) (U := U) (V := V)) :=
    (((continuous_subtype_val.comp (continuous_fst.comp continuous_fst)).mul
      (continuous_subtype_val.comp (continuous_snd.comp continuous_fst))).mul
      (continuous_subtype_val.comp continuous_snd).inv).measurable
  generalize hc : μ K * (openCellConstant (leviUnipotentMeasure hP μM μU) μV K)⁻¹ = c at heq ⊢
  have hc0 : c ≠ 0 := by
    rw [← hc]; exact mul_ne_zero hK0 (ENNReal.inv_ne_zero.mpr hγtop)
  have hctop : c ≠ ⊤ := by
    rw [← hc]; exact ENNReal.mul_ne_top hKtop (ENNReal.inv_ne_top.mpr hγ0)
  have hF' : Integrable F (((μM.prod μU).prod μV).map openCellCoord) := by
    have h1 : Integrable F (c • ((μM.prod μU).prod μV).map openCellCoord) := heq ▸ hF
    exact (integrable_smul_measure hc0 hctop).mp h1
  refine ⟨hF'.comp_measurable hφ, ?_⟩
  calc ∫ g, F g ∂μ = ∫ g, F g ∂(c • ((μM.prod μU).prod μV).map openCellCoord) := by
        rw [← heq]
    _ = c.toReal • ∫ g, F g ∂(((μM.prod μU).prod μV).map openCellCoord) :=
        integral_smul_measure _ _
    _ = c.toReal • ∫ x, F (openCellCoord x) ∂((μM.prod μU).prod μV) := by
        rw [integral_map hφ.aemeasurable hF'.aestronglyMeasurable]

/-- `δ̄(a m a⁻¹)^{1/2} δ(m)^{-1/2} = δ(m)⁻¹` when `δ̄ = δ⁻¹` on `M`. -/
theorem sqrt_mul_inv_sqrt_eq {M : Type*} [Group M] {δ δbar : M →* ℝ≥0ˣ}
    (hδbar : ∀ m, δbar m = (δ m)⁻¹) (a m : M) :
    NNReal.sqrt (δbar (a * m * a⁻¹)) * (NNReal.sqrt (δ m))⁻¹ = ((δ m : ℝ≥0))⁻¹ := by
  have h1 : (δbar (a * m * a⁻¹) : ℝ≥0) = ((δ m : ℝ≥0))⁻¹ := by
    rw [hδbar, map_mul, map_mul, map_inv, mul_comm (δ a), mul_assoc, mul_inv_cancel, mul_one,
      Units.val_inv_eq_inv_val]
  rw [h1, NNReal.sqrt_inv, ← mul_inv, NNReal.mul_self_sqrt]

include hMU in
/-- The decomposition `hsplit` of `conjugationIntegralBound_of_split` (Waldspurger, proof of
Proposition VIII.3.1): for `a ∈ M`, with `Ω` the set of `m u v⁻¹` such that `a (m u m⁻¹) a⁻¹ ∈ Γ`
and `v ∈ Γ̄` (`hΩmem`; for Waldspurger `Ω = a⁻¹ Γ a M Γ̄`), `f₁` left `Γ`-invariant and `f₂`
right `Γ̄`-invariant,
`∫_G f₁(a g a⁻¹) f₂(g) dμ = ∫_{Ωᶜ} f₁(a g a⁻¹) f₂(g) dμ + c ∫_M φ₁(a, a m a⁻¹) φ₂(a, m) dμ_M`
with `c = μ(K) γ⁻¹`, `φ₁ = cuspidalFactor` for `(V, μ_V, δ̄, Γ̄)` and `φ₂ = unipotentFactor` for
`(U, μ_U, δ, a⁻¹ Γ a)`. -/
theorem integral_conj_mul_eq_split (hhomeo : IsHomeomorph (leviUnipotentCoord hP))
    (hι : IsOpenEmbedding (openCellMap (P := P) (V := V)))
    (hnull : μ (Set.range (openCellMap (P := P) (V := V)))ᶜ = 0)
    {K : Subgroup G} (hK : MeasurableSet (K : Set G)) (hK0 : μ K ≠ 0) (hKtop : μ K ≠ ⊤)
    {δ : M →* ℝ≥0ˣ} (hν : IsConjModulus hMU μU δ) [μV.IsInvInvariant]
    (hMV : M ≤ Subgroup.normalizer (V : Set G)) {δbar : M →* ℝ≥0ˣ}
    (hδbar : ∀ m, δbar m = (δ m)⁻¹) {Γ : Set G} {Γbar : Subgroup V}
    {f₁ f₂ : G → ℂ} (hf₁ : ∀ γ ∈ Γ, ∀ x, f₁ (γ * x) = f₁ x)
    (hf₂ : ∀ γ ∈ Γbar, ∀ x, f₂ (x * (γ : G)) = f₂ x)
    (a : M) {Ω : Set G} (hΩ : MeasurableSet Ω)
    (hΩmem : ∀ (m : M) (u : U) (v : V), (m : G) * u * (v : G)⁻¹ ∈ Ω ↔
      (a : G) * (conjUnipotent hMU m u : G) * (a : G)⁻¹ ∈ Γ ∧ v ∈ Γbar)
    (hA : MeasurableSet {u : U | (a : G) * u * (a : G)⁻¹ ∈ Γ})
    (hint : Integrable (fun g => f₁ ((a : G) * g * (a : G)⁻¹) * f₂ g) μ) :
    ∫ g, f₁ ((a : G) * g * (a : G)⁻¹) * f₂ g ∂μ =
      ∫ g in Ωᶜ, f₁ ((a : G) * g * (a : G)⁻¹) * f₂ g ∂μ +
        (((μ K * (openCellConstant (leviUnipotentMeasure hP μM μU) μV K)⁻¹).toReal : ℝ) : ℂ) *
          ∫ m, cuspidalFactor hMV μV δbar (Γbar : Set V) f₁ a (a * m * a⁻¹) *
            unipotentFactor μU δ {u : U | (a : G) * u * (a : G)⁻¹ ∈ Γ} f₂ m ∂μM := by
  set h : G → ℂ := fun g => f₁ ((a : G) * g * (a : G)⁻¹) * f₂ g with hh
  set A : Set U := {u : U | (a : G) * u * (a : G)⁻¹ ∈ Γ} with hAdef
  set c := μ K * (openCellConstant (leviUnipotentMeasure hP μM μU) μV K)⁻¹
  obtain ⟨hFint, hFeq⟩ := integral_eq_smul_integral_openCellCoord hMU hP μ μM μU μV hhomeo hι
    hnull hK hK0 hKtop (hint.indicator hΩ)
  -- the integrand in open-cell coordinates
  have hpt : ∀ (m : M) (u : U) (v : V), Ω.indicator h (openCellCoord ((m, u), v)) =
      (Γbar : Set V).indicator (fun v => f₁ ((a : G) * m * (v : G)⁻¹ * (a : G)⁻¹)) v *
        A.indicator (fun u' : U => f₂ ((u' : G) * m)) (conjUnipotent hMU m u) := by
    intro m u v
    have hmem := hΩmem m u v
    simp only [openCellCoord] at hmem ⊢
    by_cases hin : (m : G) * u * (v : G)⁻¹ ∈ Ω
    · obtain ⟨huA, hvΓ⟩ := hmem.mp hin
      rw [Set.indicator_of_mem hin, Set.indicator_of_mem (show v ∈ (Γbar : Set V) from hvΓ),
        Set.indicator_of_mem (show conjUnipotent hMU m u ∈ A from huA)]
      simp only [hh, conjUnipotent]
      have e1 : (a : G) * ((m : G) * u * (v : G)⁻¹) * (a : G)⁻¹ =
          ((a : G) * ((m : G) * u * (m : G)⁻¹) * (a : G)⁻¹) *
            ((a : G) * m * (v : G)⁻¹ * (a : G)⁻¹) := by group
      have e2 : (m : G) * u * (v : G)⁻¹ = ((m : G) * u * (m : G)⁻¹) * m * ((v⁻¹ : V) : G) := by
        simp only [InvMemClass.coe_inv]; group
      rw [e1, hf₁ _ (show (a : G) * ((m : G) * u * (m : G)⁻¹) * (a : G)⁻¹ ∈ Γ from huA), e2,
        hf₂ _ (Γbar.inv_mem hvΓ)]
    · rw [Set.indicator_of_notMem hin]
      by_cases hvΓ : v ∈ Γbar
      · have huA : conjUnipotent hMU m u ∉ A := fun huA => hin (hmem.mpr ⟨huA, hvΓ⟩)
        rw [Set.indicator_of_notMem huA, mul_zero]
      · rw [Set.indicator_of_notMem (show v ∉ (Γbar : Set V) from hvΓ), zero_mul]
  -- the inner integral over `V`, after inverting `v`
  have hI₁ : ∀ m : M,
      ∫ v, (Γbar : Set V).indicator (fun v => f₁ ((a : G) * m * (v : G)⁻¹ * (a : G)⁻¹)) v ∂μV =
      ∫ v, (Γbar : Set V).indicator
      (fun v => f₁ (((a * m * a⁻¹ : M) : G) * (conjUnipotent hMV a v : G))) v ∂μV := by
    intro m
    have hφ : ∀ v : V, (Γbar : Set V).indicator
        (fun v => f₁ ((a : G) * m * (v : G)⁻¹ * (a : G)⁻¹)) v =
        (Γbar : Set V).indicator
          (fun v => f₁ (((a * m * a⁻¹ : M) : G) * (conjUnipotent hMV a v : G))) v⁻¹ := by
      intro v
      by_cases hv : v ∈ Γbar
      · rw [Set.indicator_of_mem (show v ∈ (Γbar : Set V) from hv),
          Set.indicator_of_mem (show v⁻¹ ∈ (Γbar : Set V) from Γbar.inv_mem hv)]
        simp only [conjUnipotent, Subgroup.coe_mul, InvMemClass.coe_inv]
        congr 1
        group
      · rw [Set.indicator_of_notMem (show v ∉ (Γbar : Set V) from hv),
          Set.indicator_of_notMem (show v⁻¹ ∉ (Γbar : Set V) from
            fun h' => hv (by simpa using Γbar.inv_mem h'))]
    simp_rw [hφ]
    exact integral_inv_eq_self _ μV
  -- the scalar identity
  have hs : ∀ m : M, ((NNReal.sqrt (δbar (a * m * a⁻¹)) : ℝ) : ℂ) *
      ((((NNReal.sqrt (δ m))⁻¹ : ℝ≥0) : ℝ) : ℂ) = ((((δ m : ℝ≥0)⁻¹ : ℝ≥0) : ℝ) : ℂ) := by
    intro m
    rw [← Complex.ofReal_mul, ← NNReal.coe_mul, sqrt_mul_inv_sqrt_eq hδbar a m]
  rw [← integral_add_compl hΩ hint, add_comm]
  congr 1
  rw [← integral_indicator hΩ, hFeq, Complex.real_smul]
  congr 1
  rw [integral_prod (fun x => Ω.indicator h (openCellCoord x)) hFint,
    integral_prod (fun x : M × U => ∫ v, Ω.indicator h (openCellCoord (x, v)) ∂μV)
      hFint.integral_prod_left]
  refine integral_congr_ae (Filter.Eventually.of_forall fun m => ?_)
  simp only [hpt m]
  simp_rw [integral_mul_const]
  rw [integral_const_mul,
    hν.integral_comp m (fun u' => A.indicator (fun u' : U => f₂ ((u' : G) * m)) u'),
    integral_indicator hA, hI₁ m]
  simp only [cuspidalFactor, unipotentFactor]
  rw [← hs m]
  ring

include hMU in
/-- Proposition VIII.3.1 (`ConjugationIntegralBound`) from the open-cell data: the
decomposition `hsplit` is supplied by `integral_conj_mul_eq_split` for every `a ∈ T` (with the
set `Ω(a)`), and the remaining hypotheses are the two estimates of the proof, (3) on
`Ω(a)ᶜ = S(a)` (`h3`, see `ConvolutionWeights.lintegral_conj_mul_le`) and the estimate of `J(a)`
(`hJ`, in the form of the conclusion of `lintegral_cuspidal_le`). -/
theorem conjugationIntegralBound_of_openCell (hhomeo : IsHomeomorph (leviUnipotentCoord hP))
    (hι : IsOpenEmbedding (openCellMap (P := P) (V := V)))
    (hnull : μ (Set.range (openCellMap (P := P) (V := V)))ᶜ = 0)
    {K : Subgroup G} (hK : MeasurableSet (K : Set G)) (hK0 : μ K ≠ 0) (hKtop : μ K ≠ ⊤)
    {δ : M →* ℝ≥0ˣ} (hν : IsConjModulus hMU μU δ) [μV.IsInvInvariant]
    (hMV : M ≤ Subgroup.normalizer (V : Set G)) {δbar : M →* ℝ≥0ˣ}
    (hδbar : ∀ m, δbar m = (δ m)⁻¹) {Γ : Set G} {Γbar : Subgroup V}
    {f₁ f₂ : G → ℂ} (hf₁ : ∀ γ ∈ Γ, ∀ x, f₁ (γ * x) = f₁ x)
    (hf₂ : ∀ γ ∈ Γbar, ∀ x, f₂ (x * (γ : G)) = f₂ x)
    {T : Set M} {Ω : M → Set G} (hΩ : ∀ a ∈ T, MeasurableSet (Ω a))
    (hΩmem : ∀ a ∈ T, ∀ (m : M) (u : U) (v : V), (m : G) * u * (v : G)⁻¹ ∈ Ω a ↔
      (a : G) * (conjUnipotent hMU m u : G) * (a : G)⁻¹ ∈ Γ ∧ v ∈ Γbar)
    (hA : ∀ a ∈ T, MeasurableSet {u : U | (a : G) * u * (a : G)⁻¹ ∈ Γ})
    (hint : ∀ a ∈ T, Integrable (fun g => f₁ ((a : G) * g * (a : G)⁻¹) * f₂ g) μ)
    {e : M → ℝ} {σ : G → ℝ}
    (h3 : ∀ r : ℝ, ∃ c : ℝ≥0, ∀ a ∈ T,
      ∫⁻ g in (Ω a)ᶜ, ‖f₁ ((a : G) * g * (a : G)⁻¹)‖ₑ * ‖f₂ g‖ₑ ∂μ ≤
        c * ENNReal.ofReal (e a ^ 2 * (1 + σ a) ^ (-r)))
    (hJ : ∀ r : ℝ, ∃ c : ℝ≥0, ∀ a ∈ T,
      ∫⁻ m : M, ‖cuspidalFactor hMV μV δbar (Γbar : Set V) f₁ a (a * m * a⁻¹)‖ₑ *
        ‖unipotentFactor μU δ {u : U | (a : G) * u * (a : G)⁻¹ ∈ Γ} f₂ m‖ₑ ∂μM ≤
          c * ENNReal.ofReal (e a ^ 2 * (1 + σ a) ^ (-r))) :
    ConjugationIntegralBound μ T f₁ f₂ e σ :=
  conjugationIntegralBound_of_split (S := fun a => (Ω a)ᶜ)
    (φ₁ := fun a m => cuspidalFactor hMV μV δbar (Γbar : Set V) f₁ a (a * m * a⁻¹))
    (φ₂ := fun a m => unipotentFactor μU δ {u : U | (a : G) * u * (a : G)⁻¹ ∈ Γ} f₂ m)
    (γ := (((μ K * (openCellConstant (leviUnipotentMeasure hP μM μU) μV K)⁻¹).toReal : ℝ) : ℂ))
    (fun a ha => integral_conj_mul_eq_split hMU hP μ μM μU μV hhomeo hι hnull hK hK0 hKtop hν
      hMV hδbar hf₁ hf₂ a (hΩ a ha) (hΩmem a ha) (hA a ha) (hint a ha)) h3 hJ

end Split

end Langlands.HarishChandraSchwartz
