import Langlands.Global.RankinSelberg.RealLocalNormalizedGrowth
import Langlands.Global.RankinSelberg.RealUniformWhittakerModel
import Langlands.Global.RankinSelberg.RealUnequalMellinReduction
import Langlands.Representation.Archimedean.RealStandardModuleGKModule

/-! # The normalized real unequal-rank equation is preserved by linear spanning -/

noncomputable section

open MeasureTheory
open scoped NNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGapGrowthSubmodule

open Langlands.LocalFactor.Archimedean (RealBlock)
open Langlands.RankinSelberg (LeftUnipotentQuotient rectangularMeasure rectangularMeasure_isAddHaar)
open ArchimedeanLocal (RealQuotientMeasureData realSelfDualMeasure realUnequalIntegrand realUnequalIntegral
  realUnequalDualKernel realUnequalDualIntegral realUnequalDualMeasure)
open RealJacquet (HasRealPairNormalizedGrowth)
open RealUnequalMellinReduction (sigmaFinite_quotient)

local instance gapGrowthGLMeasurable (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear n ℝ) := borel _
local instance gapGrowthGLBorel (n : ℕ) : BorelSpace (Langlands.GeneralLinear n ℝ) := ⟨rfl⟩
local instance gapGrowthUMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear.upperUnipotent n ℝ) := borel _
local instance gapGrowthUBorel (n : ℕ) : BorelSpace (Langlands.GeneralLinear.upperUnipotent n ℝ) := ⟨rfl⟩
local instance gapGrowthQMeasurable (n : ℕ) : MeasurableSpace (LeftUnipotentQuotient n ℝ) := borel _
local instance gapGrowthQBorel (n : ℕ) : BorelSpace (LeftUnipotentQuotient n ℝ) := ⟨rfl⟩

variable {r t : ℕ} (h : t < r)
local notation "GR" => Langlands.GeneralLinear (r + 1) ℝ
local notation "GT" => Langlands.GeneralLinear (t + 1) ℝ

/-- The unequal-rank integrand is additive in the larger function. -/
theorem unequalIntegrand_add (W₁ W₂ : GR → ℂ) (V : GT → ℂ) (s : ℂ) :
    realUnequalIntegrand h (W₁ + W₂) V s =
      realUnequalIntegrand h W₁ V s + realUnequalIntegrand h W₂ V s := by
  funext q
  simp only [realUnequalIntegrand, ArchimedeanLocal.unequalIntegrand, Pi.add_apply]
  ring

/-- The unequal-rank integrand is homogeneous in the larger function. -/
theorem unequalIntegrand_smul (c : ℂ) (W : GR → ℂ) (V : GT → ℂ) (s : ℂ) :
    realUnequalIntegrand h (c • W) V s = c • realUnequalIntegrand h W V s := by
  funext q
  simp only [realUnequalIntegrand, ArchimedeanLocal.unequalIntegrand, Pi.smul_apply, smul_eq_mul]
  ring

/-- The dual block kernel is additive in the larger function. -/
theorem dualKernel_add (W₁ W₂ : GR → ℂ) (V : GT → ℂ) (s : ℂ) :
    realUnequalDualKernel h (W₁ + W₂) V s =
      realUnequalDualKernel h W₁ V s + realUnequalDualKernel h W₂ V s := by
  funext p
  simp only [realUnequalDualKernel, ArchimedeanLocal.blockKernel, ArchimedeanLocal.translateFunction,
    ArchimedeanLocal.dualFunction, Pi.add_apply]
  ring

/-- The dual block kernel is homogeneous in the larger function. -/
theorem dualKernel_smul (c : ℂ) (W : GR → ℂ) (V : GT → ℂ) (s : ℂ) :
    realUnequalDualKernel h (c • W) V s = c • realUnequalDualKernel h W V s := by
  funext p
  simp only [realUnequalDualKernel, ArchimedeanLocal.blockKernel, ArchimedeanLocal.translateFunction,
    ArchimedeanLocal.dualFunction, Pi.smul_apply, smul_eq_mul]
  ring

/-- For an integrable dual kernel, the iterated dual integral is the integral over the product. -/
theorem dualIntegral_eq_prod (b : ℝˣ) (D : RealQuotientMeasureData t) (W : GR → ℂ) (V : GT → ℂ)
    (s : ℂ) (hI : Integrable (realUnequalDualKernel h W V s) (realUnequalDualMeasure (r := r) b D)) :
    realUnequalDualIntegral h b D W V s =
      ∫ p, realUnequalDualKernel h W V s p ∂realUnequalDualMeasure (r := r) b D := by
  let : SigmaFinite D.measure := sigmaFinite_quotient D
  let : (realSelfDualMeasure b).measure.IsAddHaarMeasure := (realSelfDualMeasure b).isAddHaar
  let : (rectangularMeasure (realSelfDualMeasure b) (r - (t + 1)) (t + 1)).IsAddHaarMeasure :=
    rectangularMeasure_isAddHaar _ _ _
  exact (integral_prod _ hI).symm

/-- The unequal-rank integral is the quotient integral of its integrand. -/
theorem integral_eq (D : RealQuotientMeasureData t) (W : GR → ℂ) (V : GT → ℂ) (s : ℂ) :
    realUnequalIntegral h D W V s = ∫ q, realUnequalIntegrand h W V s q ∂D.measure := rfl

/-- For a fixed smaller function `V`, the larger functions whose unequal-rank integrals converge on
a right half-plane and admit the normalized equation with strip growth for the given data. -/
def unequalGrowthSubmodule (D : RealQuotientMeasureData t) (b : ℝˣ) (V : GT → ℂ)
    (xs ys xsd ysd : List RealBlock) (eb : ℝˣ) (c : ℝ≥0) (hc : 0 < c) (sign : ℂ) :
    Submodule ℂ (GR → ℂ) where
  carrier := {W | ∃ σ : ℝ, (∀ s : ℂ, σ < s.re →
      Integrable (realUnequalIntegrand h W V s) D.measure ∧
      Integrable (realUnequalDualKernel h W V s) (realUnequalDualMeasure (r := r) b D)) ∧
    HasRealPairNormalizedGrowth xs ys xsd ysd eb c hc sign
      (realUnequalIntegral h D W V) (realUnequalDualIntegral h b D W V)}
  zero_mem' := by
    have h₀ (s : ℂ) : realUnequalIntegrand h (0 : GR → ℂ) V s = 0 := by
      simpa using unequalIntegrand_smul h 0 0 V s
    have hd₀ (s : ℂ) : realUnequalDualKernel h (0 : GR → ℂ) V s = 0 := by
      simpa using dualKernel_smul h 0 0 V s
    refine ⟨0, fun s _ => ⟨?_, ?_⟩, ?_⟩
    · rw [h₀]
      exact integrable_zero _ _ _
    · rw [hd₀]
      exact integrable_zero _ _ _
    · refine HasRealPairNormalizedGrowth.zero.congr (τ := 0) (fun s _ => ?_) (fun s _ => ?_)
      · change (0 : ℂ) = realUnequalIntegral h D 0 V s
        rw [integral_eq, h₀]
        simp
      · change (0 : ℂ) = realUnequalDualIntegral h b D 0 V s
        rw [dualIntegral_eq_prod h b D 0 V s (by rw [hd₀]; exact integrable_zero _ _ _), hd₀]
        simp
  add_mem' := by
    rintro W₁ W₂ ⟨σ₁, hI₁, hG₁⟩ ⟨σ₂, hI₂, hG₂⟩
    refine ⟨max σ₁ σ₂, fun s hs => ?_, ?_⟩
    · obtain ⟨a₁, b₁⟩ := hI₁ s ((le_max_left _ _).trans_lt hs)
      obtain ⟨a₂, b₂⟩ := hI₂ s ((le_max_right _ _).trans_lt hs)
      rw [unequalIntegrand_add, dualKernel_add]
      exact ⟨a₁.add a₂, b₁.add b₂⟩
    · refine (hG₁.add hG₂).congr (τ := max σ₁ σ₂) (fun s hs => ?_) (fun s hs => ?_)
      · obtain ⟨a₁, -⟩ := hI₁ s ((le_max_left _ _).trans_lt hs)
        obtain ⟨a₂, -⟩ := hI₂ s ((le_max_right _ _).trans_lt hs)
        change realUnequalIntegral h D W₁ V s + realUnequalIntegral h D W₂ V s =
          realUnequalIntegral h D (W₁ + W₂) V s
        rw [integral_eq, integral_eq, integral_eq, unequalIntegrand_add]
        exact (integral_add a₁ a₂).symm
      · obtain ⟨-, b₁⟩ := hI₁ s ((le_max_left _ _).trans_lt hs)
        obtain ⟨-, b₂⟩ := hI₂ s ((le_max_right _ _).trans_lt hs)
        change realUnequalDualIntegral h b D W₁ V s + realUnequalDualIntegral h b D W₂ V s =
          realUnequalDualIntegral h b D (W₁ + W₂) V s
        have b₃ : Integrable (realUnequalDualKernel h (W₁ + W₂) V s)
            (realUnequalDualMeasure (r := r) b D) := by
          rw [dualKernel_add]
          exact b₁.add b₂
        rw [dualIntegral_eq_prod h b D W₁ V s b₁, dualIntegral_eq_prod h b D W₂ V s b₂,
          dualIntegral_eq_prod h b D _ V s b₃, dualKernel_add]
        exact (integral_add b₁ b₂).symm
  smul_mem' := by
    rintro c₀ W ⟨σ, hI, hG⟩
    refine ⟨σ, fun s hs => ?_, ?_⟩
    · obtain ⟨a₁, b₁⟩ := hI s hs
      rw [unequalIntegrand_smul, dualKernel_smul]
      exact ⟨a₁.smul c₀, b₁.smul c₀⟩
    · refine (hG.const_mul c₀).congr (τ := σ) (fun s hs => ?_) (fun s hs => ?_)
      · change c₀ * realUnequalIntegral h D W V s = realUnequalIntegral h D (c₀ • W) V s
        rw [integral_eq, integral_eq, unequalIntegrand_smul]
        simp only [Pi.smul_apply, smul_eq_mul]
        exact (integral_const_mul c₀ _).symm
      · obtain ⟨-, b₁⟩ := hI s hs
        change c₀ * realUnequalDualIntegral h b D W V s = realUnequalDualIntegral h b D (c₀ • W) V s
        have b₂ : Integrable (realUnequalDualKernel h (c₀ • W) V s)
            (realUnequalDualMeasure (r := r) b D) := by
          rw [dualKernel_smul]
          exact b₁.smul c₀
        rw [dualIntegral_eq_prod h b D W V s b₁, dualIntegral_eq_prod h b D _ V s b₂, dualKernel_smul]
        simp only [Pi.smul_apply, smul_eq_mul]
        exact (integral_const_mul c₀ _).symm

/-- Right translation by an element of the orthogonal group preserves a uniform real Whittaker
model. -/
theorem translate_mem_model {ds : List RealBlock} {a : ℝˣ} {W : GR → ℂ}
    (hW : W ∈ realUniformWhittakerModel r ds a) {k : GR}
    (hk : k ∈ Langlands.Archimedean.unitaryCompact ℝ (r + 1)) :
    ArchimedeanLocal.translateFunction k W ∈ realUniformWhittakerModel r ds a := by
  let T := Whittaker.rightTranslation ℂ GR k
  have hle : realUniformWhittakerModel r ds a ≤ (realUniformWhittakerModel r ds a).comap T := by
    refine iSup_le fun B => iSup_le fun hB => ?_
    rintro _ ⟨f, rfl⟩
    let f' : Automorphic.realStandardKFinite (r + 1) ds :=
      ⟨T f.val, Langlands.Archimedean.rightTranslation_mem_kFiniteFunctions_realStandardModule
        (r + 1) ds f.2 hk⟩
    have hB' : B f' = T (B f) := hB.1.2.2.2.1 ⟨k, hk⟩ f f' rfl
    change T (B f) ∈ realUniformWhittakerModel r ds a
    rw [← hB']
    exact Submodule.mem_iSup_of_mem B (Submodule.mem_iSup_of_mem hB ⟨f', rfl⟩)
  exact hle hW

end Langlands.Global.RankinSelbergGlobal.RealGapGrowthSubmodule
