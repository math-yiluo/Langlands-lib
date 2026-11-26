import Langlands.Global.RankinSelberg.ArchimedeanRealPairIdentity
import Langlands.Global.RankinSelberg.RealUnequalPairConvergence
import Langlands.Representation.RankinSelberg.LastRowCompactOrbitProof

/-! # The determinant as Mellin variable of the real unequal-rank kernels -/

noncomputable section

open MeasureTheory

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealUnequalMellinReduction

open Langlands.RankinSelberg (LeftUnipotentQuotient)
open ArchimedeanLocal
open ArchimedeanRealPairIdentity (norm_kernel kernel_zero_eq ofReal_cpow_eq_exp)

attribute [local instance] archimedeanRealGLMeasurable archimedeanRealGLBorel
  archimedeanRealNMeasurable archimedeanRealNBorel
  archimedeanRealQMeasurable archimedeanRealQBorel

local notation "G" => fun n => Langlands.GeneralLinear n ℝ
local notation "Q" => fun t => LeftUnipotentQuotient t ℝ
local notation "Δ" => fun g => realNormalizedAbs (Matrix.det (Units.val g))

/-- The absolute value of the determinant on the smaller left-unipotent quotient. -/
def quotientDetAbs {t : ℕ} (q : Q t) : ℝ :=
  ArchimedeanRealPairIdentity.quotientDetAbs q

theorem quotientDetAbs_pos {t : ℕ} (q : Q t) : 0 < quotientDetAbs q :=
  ArchimedeanRealPairIdentity.quotientDetAbs_pos q

theorem continuous_quotientDetAbs {t : ℕ} : Continuous (quotientDetAbs (t := t)) :=
  ArchimedeanRealPairIdentity.continuous_quotientDetAbs

/-- The determinant is the Mellin variable for the ordinary real unequal kernel. -/
theorem realUnequalIntegrand_eq_mul {r t : ℕ} (h : t < r) (W : G (r + 1) → ℂ)
    (V : G (t + 1) → ℂ) (s : ℂ) (q : Q t) :
    realUnequalIntegrand h W V s q =
      realUnequalIntegrand h W V 0 q * (quotientDetAbs q : ℂ) ^ s :=
  ArchimedeanRealPairIdentity.realUnequalIntegrand_eq_mul h W V s q

/-- The same smaller quotient determinant is the Mellin variable for the block kernel. -/
theorem realUnequalDualKernel_eq_mul {r t : ℕ} (h : t < r) (W : G (r + 1) → ℂ)
    (V : G (t + 1) → ℂ) (s : ℂ) (p : Q t × Matrix (Fin (r - (t + 1))) (Fin (t + 1)) ℝ) :
    realUnequalDualKernel h W V s p =
      realUnequalDualKernel h W V 0 p * (quotientDetAbs p.1 : ℂ) ^ s :=
  ArchimedeanRealPairIdentity.realUnequalDualKernel_eq_mul h W V s p

/-- The compatible measure on the real left-unipotent quotient is sigma finite. -/
theorem sigmaFinite_quotient {t : ℕ} (D : RealQuotientMeasureData t) : SigmaFinite D.measure :=
  ArchimedeanRealPairIdentity.sigmaFinite_measure D

/-- Integrability on a right half-plane of a kernel with Mellin variable `δ` gives
measurability of the kernel at `0` and integrability of its real-power moments. -/
theorem halfPlane_mellinData {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (A : ℂ → X → ℂ) (δ : X → ℝ) (hδm : Measurable δ) (hδ : ∀ x, 0 < δ x)
    (hA : ∀ s x, A s x = A 0 x * (δ x : ℂ) ^ s) (σ : ℝ)
    (hI : ∀ s : ℂ, σ < s.re → Integrable (A s) μ) :
    AEStronglyMeasurable (A 0) μ ∧
      ∀ b : ℝ, σ + 1 ≤ b → Integrable (fun x => ‖A 0 x‖ * δ x ^ b) μ := by
  have hb (b : ℝ) (hb : σ + 1 ≤ b) : σ < ((b : ℝ) : ℂ).re := by
    rw [Complex.ofReal_re]
    linarith
  refine ⟨?_, fun b h => (hI b (hb b h)).norm.congr (ae_of_all _ (norm_kernel hδ hA b))⟩
  let b : ℂ := (σ + 1 : ℝ)
  have hM : Measurable (fun x => (δ x : ℂ) ^ (-b)) :=
    (Complex.measurable_ofReal.comp hδm).pow_const _
  exact ((hI b (hb (σ + 1) le_rfl)).aestronglyMeasurable.mul hM.aestronglyMeasurable).congr
    (ae_of_all _ fun x => (kernel_zero_eq hδ hA b x).symm)

end Langlands.Global.RankinSelbergGlobal.RealUnequalMellinReduction
