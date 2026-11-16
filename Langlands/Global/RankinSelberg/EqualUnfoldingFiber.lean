import Langlands.Global.RankinSelberg.EqualUnfoldingSection

/-! # The fiber computation in the equal-rank unfolding -/

noncomputable section
universe u
open NumberField MeasureTheory Set
open scoped ENNReal Pointwise
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.EqualUnfolding

open Langlands.Global Unfolding

section Abstract

variable {H Z : Type*} [Group H] [Group Z] [MeasurableSpace H] [MeasurableSpace Z]
  [MeasurableMul₂ H] [MeasurableInv H] [MeasurableMul₂ Z] [MeasurableInv Z]
  (μ : Measure H) [μ.IsMulLeftInvariant] [SFinite μ]
  (ν : Measure Z) [ν.IsMulLeftInvariant] [SFinite ν]
  {σ : Z →* H} (Γ₁ : Subgroup Z) [Countable Γ₁] (P : Subgroup H) [Countable P]

/-- The fiber computation for nonnegative functions. Let `σ : Z → H` be a measurable
homomorphism with central image, `Γ₁ ≤ Z` and `P ≤ H` countable subgroups with fundamental
domains `D₁` and `DP`, and `A`, `S` measurable sets such that, for every `w`, the translates
`σ(b) p⁻¹ w` (`b ∈ Γ₁`, `p ∈ P`) lie in `A` exactly once when `w ∈ S` and never otherwise,
and such that the slice `{z ∈ D₁ : σ(z)⁻¹ x ∈ S}` has measure one for every `x`. Then for every
left `P`-invariant `h`, integrating `h(σ(z) x)` over `A × Z` gives the integral of `h` over
`DP`. -/
theorem lintegral_fiber (hσm : Measurable σ) (hσc : ∀ z x, σ z * x = x * σ z)
    {D₁ : Set Z} (hD₁ : IsFundamentalDomain Γ₁ D₁ ν)
    {DP : Set H} (hDP : IsFundamentalDomain P DP μ)
    {A S : Set H} (hA : MeasurableSet A) (hS : MeasurableSet S)
    (hcount : ∀ w : H, ∑' b : Γ₁, ∑' p : P,
      A.indicator (1 : H → ℝ≥0∞) (σ b * ((p : H)⁻¹ * w)) = S.indicator 1 w)
    (hfiber : ∀ x : H, ν (D₁ ∩ {z | (σ z)⁻¹ * x ∈ S}) = 1)
    {h : H → ℝ≥0∞} (hh : Measurable h) (hP : ∀ (p : P) (x : H), h ((p : H) * x) = h x) :
    ∫⁻ x in A, ∫⁻ z, h (σ z * x) ∂ν ∂μ = ∫⁻ x in DP, h x ∂μ := by
  set c : H → ℝ≥0∞ := fun y => ∫⁻ z, A.indicator 1 ((σ z)⁻¹ * y) ∂ν with hc
  have hmeasA : Measurable fun q : Z × H => A.indicator (1 : H → ℝ≥0∞) ((σ q.1)⁻¹ * q.2) :=
    (measurable_one.indicator hA).comp ((hσm.comp measurable_fst).inv.mul measurable_snd)
  have hcm : Measurable c := hmeasA.lintegral_prod_left'
  have hmeasA' : ∀ y : H, Measurable fun z : Z => A.indicator (1 : H → ℝ≥0∞) ((σ z)⁻¹ * y) :=
    fun y => hmeasA.comp (measurable_id.prodMk measurable_const)
  -- step 1: translate the inner integral
  have h1 : ∀ z : Z, ∫⁻ x in A, h (σ z * x) ∂μ =
      ∫⁻ y, h y * A.indicator 1 ((σ z)⁻¹ * y) ∂μ := by
    intro z
    rw [← lintegral_mul_left_eq_self (fun y => h y * A.indicator 1 ((σ z)⁻¹ * y)) (σ z),
      ← lintegral_indicator hA]
    congr 1
    ext x
    simp only [inv_mul_cancel_left]
    by_cases hx : x ∈ A <;> simp [hx]
  -- step 2: exchange the integrals twice
  have h2 : ∫⁻ x in A, ∫⁻ z, h (σ z * x) ∂ν ∂μ = ∫⁻ y, h y * c y ∂μ := by
    rw [lintegral_lintegral_swap (μ := μ.restrict A) (ν := ν)
      (f := fun x z => h (σ z * x))
      ((hh.comp ((hσm.comp measurable_snd).mul measurable_fst)).aemeasurable)]
    simp_rw [h1]
    rw [lintegral_lintegral_swap (μ := ν) (ν := μ)
      (f := fun z y => h y * A.indicator 1 ((σ z)⁻¹ * y))
      (((hh.comp measurable_snd).mul hmeasA).aemeasurable)]
    refine lintegral_congr fun y => ?_
    rw [hc]
    exact lintegral_const_mul _ (hmeasA' y)
  -- step 3: the counting identity
  have hcount' : ∀ x : H, ∑' p : P, c (p⁻¹ • x) = 1 := by
    intro x
    have hsmul : ∀ p : P, p⁻¹ • x = (p : H)⁻¹ * x := fun p => by
      rw [Subgroup.smul_def, smul_eq_mul, Subgroup.coe_inv]
    have e1 : ∑' p : P, c (p⁻¹ • x) =
        ∫⁻ z, ∑' p : P, A.indicator 1 ((σ z)⁻¹ * ((p : H)⁻¹ * x)) ∂ν := by
      rw [lintegral_tsum fun p : P => (hmeasA' ((p : H)⁻¹ * x)).aemeasurable]
      refine tsum_congr fun p => ?_
      rw [hsmul]
    have hterm : ∀ (z : Z) (b : Γ₁) (p : P),
        A.indicator (1 : H → ℝ≥0∞) ((σ (b⁻¹ • z))⁻¹ * ((p : H)⁻¹ * x)) =
          A.indicator 1 (σ b * ((p : H)⁻¹ * ((σ z)⁻¹ * x))) := by
      intro z b p
      have hc1 : ∀ y : H, σ z⁻¹ * y = y * σ z⁻¹ := hσc z⁻¹
      congr 1
      rw [Subgroup.smul_def, smul_eq_mul, Subgroup.coe_inv, map_mul, map_inv, mul_inv_rev,
        inv_inv, ← map_inv σ z, hc1 (σ b), mul_assoc, ← mul_assoc (σ z⁻¹), hc1 ((p : H)⁻¹),
        mul_assoc]
    have hmeasB : ∀ (b : Γ₁) (p : P), Measurable fun z : Z =>
        A.indicator (1 : H → ℝ≥0∞) (σ b * ((p : H)⁻¹ * ((σ z)⁻¹ * x))) := fun b p =>
      (measurable_one.indicator hA).comp
        (((hσm.inv.mul_const x).const_mul ((p : H)⁻¹)).const_mul (σ b))
    rw [e1, hD₁.lintegral_eq_tsum']
    simp_rw [hterm]
    rw [← lintegral_tsum fun b => (Measurable.tsum fun p => hmeasB b p).aemeasurable]
    simp_rw [hcount]
    have hind : ∀ z : Z, S.indicator (1 : H → ℝ≥0∞) ((σ z)⁻¹ * x) =
        {z : Z | (σ z)⁻¹ * x ∈ S}.indicator 1 z := by
      intro z
      by_cases hz : (σ z)⁻¹ * x ∈ S
      · rw [indicator_of_mem hz, indicator_of_mem (show z ∈ {z : Z | (σ z)⁻¹ * x ∈ S} from hz)]
        rfl
      · rw [indicator_of_notMem hz,
          indicator_of_notMem (show z ∉ {z : Z | (σ z)⁻¹ * x ∈ S} from hz)]
    simp_rw [hind]
    have hmS : MeasurableSet {z : Z | (σ z)⁻¹ * x ∈ S} :=
      hS.preimage (hσm.inv.mul_const x)
    rw [lintegral_indicator_one hmS, Measure.restrict_apply hmS, inter_comm]
    exact hfiber x
  -- step 4: fold over `P`
  rw [h2, hDP.lintegral_eq_tsum']
  have h3 : ∀ p : P, ∫⁻ x in DP, (fun y => h y * c y) (p⁻¹ • x) ∂μ =
      ∫⁻ x in DP, h x * c (p⁻¹ • x) ∂μ := by
    intro p
    refine lintegral_congr fun x => ?_
    simp only
    congr 1
    simpa [Subgroup.smul_def] using hP p⁻¹ x
  simp_rw [h3]
  rw [← lintegral_tsum (f := fun (p : P) x => h x * c (p⁻¹ • x))
    (fun p => (hh.mul (hcm.comp (measurable_const_smul _))).aemeasurable)]
  simp_rw [ENNReal.tsum_mul_left, hcount', mul_one]

/-- The fiber computation as an identity of measures on `P \ H`: the image of
`A × Z` under `(x, z) ↦ P σ(z) x` is the image of the fundamental domain `DP`. -/
theorem map_fiber (hσm : Measurable σ) (hσc : ∀ z x, σ z * x = x * σ z)
    {D₁ : Set Z} (hD₁ : IsFundamentalDomain Γ₁ D₁ ν)
    {DP : Set H} (hDP : IsFundamentalDomain P DP μ)
    {A S : Set H} (hA : MeasurableSet A) (hS : MeasurableSet S)
    (hcount : ∀ w : H, ∑' b : Γ₁, ∑' p : P,
      A.indicator (1 : H → ℝ≥0∞) (σ b * ((p : H)⁻¹ * w)) = S.indicator 1 w)
    (hfiber : ∀ x : H, ν (D₁ ∩ {z | (σ z)⁻¹ * x ∈ S}) = 1) :
    Measure.map (fun q : H × Z => LeftCosetSpace.mk P (σ q.2 * q.1)) ((μ.restrict A).prod ν) =
      Measure.map (LeftCosetSpace.mk P) (μ.restrict DP) := by
  have hΨ : Measurable fun q : H × Z => LeftCosetSpace.mk P (σ q.2 * q.1) :=
    (LeftCosetSpace.measurable_mk P).comp ((hσm.comp measurable_snd).mul measurable_fst)
  ext T hT
  have hpre : MeasurableSet (LeftCosetSpace.mk P ⁻¹' T) := LeftCosetSpace.measurable_mk P hT
  rw [Measure.map_apply hΨ hT, Measure.map_apply (LeftCosetSpace.measurable_mk P) hT,
    ← lintegral_indicator_one (hΨ hT),
    lintegral_prod _ ((measurable_one.indicator (hΨ hT)).aemeasurable),
    ← lintegral_indicator_one hpre]
  have key : ∀ y : H, (LeftCosetSpace.mk P ⁻¹' T).indicator (1 : H → ℝ≥0∞) y =
      T.indicator 1 (LeftCosetSpace.mk P y) := fun y =>
    Set.indicator_comp_right (s := T) (LeftCosetSpace.mk P)
      (g := (1 : LeftCosetSpace P → ℝ≥0∞)) (x := y)
  have hinv : ∀ (p : P) (x : H), (LeftCosetSpace.mk P ⁻¹' T).indicator (1 : H → ℝ≥0∞)
      ((p : H) * x) = (LeftCosetSpace.mk P ⁻¹' T).indicator 1 x := by
    intro p x
    rw [key, key, LeftCosetSpace.mk_subgroup_mul]
  exact lintegral_fiber μ ν Γ₁ P hσm hσc hD₁ hDP hA hS hcount hfiber
    (measurable_one.indicator hpre) hinv

/-- The fiber computation for complex functions: for a measurable left `P`-invariant `K`
integrable on `DP`, the function `(x, z) ↦ K(σ(z) x)` is integrable on `A × Z` with the same
integral. -/
theorem integrable_and_integral_fiber (hσm : Measurable σ) (hσc : ∀ z x, σ z * x = x * σ z)
    {D₁ : Set Z} (hD₁ : IsFundamentalDomain Γ₁ D₁ ν)
    {DP : Set H} (hDP : IsFundamentalDomain P DP μ)
    {A S : Set H} (hA : MeasurableSet A) (hS : MeasurableSet S)
    (hcount : ∀ w : H, ∑' b : Γ₁, ∑' p : P,
      A.indicator (1 : H → ℝ≥0∞) (σ b * ((p : H)⁻¹ * w)) = S.indicator 1 w)
    (hfiber : ∀ x : H, ν (D₁ ∩ {z | (σ z)⁻¹ * x ∈ S}) = 1)
    {K : H → ℂ} (hK : Measurable K) (hKP : ∀ (p : P) (x : H), K ((p : H) * x) = K x)
    (hint : IntegrableOn K DP μ) :
    Integrable (fun q : H × Z => K (σ q.2 * q.1)) ((μ.restrict A).prod ν) ∧
      ∫ q, K (σ q.2 * q.1) ∂((μ.restrict A).prod ν) = ∫ x in DP, K x ∂μ := by
  set Kb := LeftCosetSpace.lift P K hKP with hKb_def
  have hKb : Measurable Kb := measurable_from_quotient.mpr hK
  set Ψ : H × Z → LeftCosetSpace P := fun q => LeftCosetSpace.mk P (σ q.2 * q.1) with hΨ_def
  have hΨ : Measurable Ψ :=
    (LeftCosetSpace.measurable_mk P).comp ((hσm.comp measurable_snd).mul measurable_fst)
  have hcomp : (fun q : H × Z => K (σ q.2 * q.1)) = Kb ∘ Ψ := rfl
  have hmap : Measure.map Ψ ((μ.restrict A).prod ν) =
      Measure.map (LeftCosetSpace.mk P) (μ.restrict DP) :=
    map_fiber μ ν Γ₁ P hσm hσc hD₁ hDP hA hS hcount hfiber
  have hKbint : Integrable Kb (Measure.map (LeftCosetSpace.mk P) (μ.restrict DP)) :=
    (integrable_map_measure hKb.aestronglyMeasurable
      (LeftCosetSpace.measurable_mk P).aemeasurable).mpr hint
  refine ⟨?_, ?_⟩
  · rw [hcomp, ← integrable_map_measure hKb.aestronglyMeasurable hΨ.aemeasurable]
    rw [hmap]
    exact hKbint
  · show ∫ q, Kb (Ψ q) ∂((μ.restrict A).prod ν) = _
    rw [← integral_map hΨ.aemeasurable hKb.aestronglyMeasurable, hmap,
      integral_map (LeftCosetSpace.measurable_mk P).aemeasurable hKb.aestronglyMeasurable]
    rfl

end Abstract

end Langlands.Global.RankinSelbergGlobal.EqualUnfolding
