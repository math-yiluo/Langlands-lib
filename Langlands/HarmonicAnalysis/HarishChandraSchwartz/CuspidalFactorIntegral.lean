import Langlands.HarmonicAnalysis.HarishChandraSchwartz.CuspidalFactorTail

/-! # The Levi integral of the two cuspidal-split factors

The full constant-term estimate bounds the second factor. Together with
the first factor's tail bound, compact Xi averaging and weighted Xi-square
integrability control their Levi integral.
-/

noncomputable section

open MeasureTheory
open scoped NNReal ENNReal

namespace Langlands.HarishChandraSchwartz

universe u

section Unipotent

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] {M U : Subgroup G}
  {hMU : M ≤ Subgroup.normalizer (U : Set G)} {ν : Measure U} {δ : M →* ℝ≥0ˣ}
  {Ξ σ : G → ℝ} {ΞM σM : M → ℝ}

/-- Uniform Levi decay of the second factor, independently of the
truncation subset assigned to the conjugator. -/
def UnipotentFactorDecayBound (ν : Measure U) (δ : M →* ℝ≥0ˣ)
    (A : M → Set U) (f : G → ℂ) (ΞM σM : M → ℝ) : Prop :=
  ∀ d : ℝ, ∃ c : ℝ≥0, ∀ a m : M,
    ‖unipotentFactor ν δ (A a) f m‖ₑ ≤
      c * ENNReal.ofReal (ΞM m * (1 + σM m) ^ (-d))

/-- The full constant-term bound controls the second split factor for
any truncation family. -/
theorem unipotentFactorDecayBound_of_constantTermEstimate
    (hν : IsConjModulus hMU ν δ)
    (h45 : ConstantTermEstimate ν δ Ξ σ ΞM σM)
    (hΞ : ∀ g, 0 < Ξ g) (hσ : ∀ g, 0 ≤ σ g)
    (A : M → Set U) {f : G → ℂ} (hf : ∀ r : ℝ, nu Ξ σ r f < ⊤) :
    UnipotentFactorDecayBound ν δ A f ΞM σM := by
  intro d
  obtain ⟨d', c, hc⟩ := h45.lintegral_mul_right_le hν hΞ hσ d
  let F : ℝ≥0∞ := nu Ξ σ d' f
  have hF : F ≠ ⊤ := (hf d').ne
  refine ⟨(c * F).toNNReal, fun a m => ?_⟩
  rw [ENNReal.coe_toNNReal (ENNReal.mul_ne_top ENNReal.coe_ne_top hF),
    unipotentFactor, enorm_nnreal_mul]
  calc
    ((((NNReal.sqrt (δ m))⁻¹ : ℝ≥0) : ℝ≥0∞)) *
        ‖∫ u in A a, f ((u : G) * m) ∂ν‖ₑ ≤
      ((((NNReal.sqrt (δ m))⁻¹ : ℝ≥0) : ℝ≥0∞)) *
        ∫⁻ u : U, ‖f ((u : G) * m)‖ₑ ∂ν := by
      apply mul_le_mul_of_nonneg_left _ zero_le
      exact (enorm_integral_le_lintegral_enorm _).trans (setLIntegral_le_lintegral _ _)
    _ ≤ c * F * ENNReal.ofReal (ΞM m * (1 + σM m) ^ (-d)) := hc f hF m

end Unipotent

section Integral

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] {M U V : Subgroup G}
  {hMU : M ≤ Subgroup.normalizer (U : Set G)}
  {νU : Measure U} {δU : M →* ℝ≥0ˣ}
  {νV : Measure V} {δV : M →* ℝ≥0ˣ}
  {ΞM σM : M → ℝ} {KM : Subgroup M} [CompactSpace KM]
  [SecondCountableTopology M] {muM : Measure M} [SFinite muM]
  [muM.IsMulLeftInvariant] [muM.IsMulRightInvariant]

/-- The Levi integral of the split factors retains every negative power of
the tail cutoff, multiplied by the conjugator's squared Levi Xi. -/
theorem lintegral_cuspidalFactors_le_of_tail
    (hwM : ConvolutionWeights muM KM ΞM σM)
    (hσr : ∀ k ∈ KM, ∀ m : M, σM (m * k) = σM m)
    {Γ : Set U} {A : M → Set V} {f₁ f₂ : G → ℂ} {T : Set M} {t : M → ℝ}
    (h₁ : CuspidalFactorTailBound hMU νU δU Γ f₁ T t ΞM σM)
    (h₂ : UnipotentFactorDecayBound νV δV A f₂ ΞM σM)
    {p : ℝ} (hp : 0 ≤ p) :
    ∃ c : ℝ≥0, ∀ a ∈ T,
      ∫⁻ m : M, ‖cuspidalFactor hMU νU δU Γ f₁ a (a * m * a⁻¹)‖ₑ *
          ‖unipotentFactor νV δV (A a) f₂ m‖ₑ ∂muM ≤
        c * (((δU a : ℝ≥0)⁻¹ : ℝ≥0) : ℝ≥0∞) *
          ENNReal.ofReal (t a ^ (-p)) * ENNReal.ofReal (ΞM a ^ 2) := by
  obtain ⟨d₀, hd₀⟩ := hwM.square
  obtain ⟨c₁, hc₁⟩ := h₁ 0 p hp
  obtain ⟨c₂, hc₂⟩ := h₂ d₀
  let W : M → ℝ≥0∞ := fun m =>
    ENNReal.ofReal (ΞM m * (1 + σM m) ^ (-(d₀ : ℝ)))
  let I : ℝ≥0∞ := ∫⁻ m : M,
    ENNReal.ofReal (ΞM m ^ 2 * (1 + σM m) ^ (-(d₀ : ℝ))) ∂muM
  have hI : I ≠ ⊤ := hd₀.ne
  have hpos (m : M) : 0 < 1 + σM m := by linarith [hwM.nonneg m]
  have hWm : Measurable W :=
    ENNReal.measurable_ofReal.comp
      (hwM.continuous_xi.mul
        ((continuous_const.add hwM.continuous_sigma).rpow_const
          (fun m => Or.inl (hpos m).ne'))).measurable
  have hWl : ∀ k ∈ KM, ∀ m, W (k * m) = W m := by
    intro k hk m
    simp only [W, hwM.xi_mul_left k hk, hwM.sigma_mul_left k hk]
  have hWr : ∀ k ∈ KM, ∀ m, W (m * k) = W m := by
    intro k hk m
    simp only [W, hwM.xi_mul_right hk, hσr k hk]
  have hIW : ∫⁻ m : M, ENNReal.ofReal (ΞM m) * W m ∂muM = I := by
    apply lintegral_congr
    intro m
    dsimp [W]
    rw [← ENNReal.ofReal_mul (hwM.pos m).le]
    congr 1
    ring
  let C : ℝ≥0∞ := (c₁ : ℝ≥0∞) * c₂ * I
  have hC : C ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top) hI
  refine ⟨C.toNNReal, fun a ha => ?_⟩
  rw [ENNReal.coe_toNNReal hC]
  let R : ℝ≥0∞ := (((δU a : ℝ≥0)⁻¹ : ℝ≥0) : ℝ≥0∞) *
    ENNReal.ofReal (t a ^ (-p))
  have hR : R ≠ ⊤ := ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top
  have hpt (m : M) :
      ‖cuspidalFactor hMU νU δU Γ f₁ a (a * m * a⁻¹)‖ₑ *
        ‖unipotentFactor νV δV (A a) f₂ m‖ₑ ≤
      ((c₁ : ℝ≥0∞) * c₂ * R) *
        (ENNReal.ofReal (ΞM (a * m * a⁻¹)) * W m) := by
    have hfirst := hc₁ a ha (a * m * a⁻¹)
    simp only [neg_zero, Real.rpow_zero, mul_one] at hfirst
    have hsecond := hc₂ a m
    calc
      _ ≤ ((c₁ : ℝ≥0∞) * (((δU a : ℝ≥0)⁻¹ : ℝ≥0) : ℝ≥0∞) *
            ENNReal.ofReal (t a ^ (-p)) * ENNReal.ofReal (ΞM (a * m * a⁻¹))) *
          ((c₂ : ℝ≥0∞) * W m) := mul_le_mul' hfirst hsecond
      _ = _ := by ring
  calc
    _ ≤ ∫⁻ m : M, ((c₁ : ℝ≥0∞) * c₂ * R) *
        (ENNReal.ofReal (ΞM (a * m * a⁻¹)) * W m) ∂muM := lintegral_mono hpt
    _ = ((c₁ : ℝ≥0∞) * c₂ * R) *
        ∫⁻ m : M, ENNReal.ofReal (ΞM (a * m * a⁻¹)) * W m ∂muM :=
      lintegral_const_mul' _ _
        (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top) hR)
    _ = C * R * ENNReal.ofReal (ΞM a ^ 2) := by
      rw [hwM.lintegral_xi_mul_mul hWm hWl hWr, hwM.xi_inv, hIW,
        ← ENNReal.ofReal_mul (hwM.pos a).le, ← sq]
      dsimp [C]
      ring
    _ = _ := by dsimp [R]; ring

end Integral

end Langlands.HarishChandraSchwartz
