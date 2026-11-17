import Langlands.Global.RankinSelberg.RealPlaceWhittakerCovariance
import Langlands.Global.RankinSelberg.RealJacquetConventionReduction

/-! # Reflection in the real equal-rank dual integral -/

noncomputable section
universe u

open NumberField MeasureTheory Langlands.RankinSelberg
open Langlands.Global.RankinSelbergGlobal.ArchimedeanLocal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000

namespace Langlands.Global.RankinSelbergGlobal
namespace RealPlaceReflection

local instance (r : ℕ) : MeasurableSpace (Langlands.GeneralLinear (r + 1) ℝ) := borel _
local instance (r : ℕ) : BorelSpace (Langlands.GeneralLinear (r + 1) ℝ) := ⟨rfl⟩
local instance (r : ℕ) : MeasurableSpace (GeneralLinear.upperUnipotent (r + 1) ℝ) := borel _
local instance (r : ℕ) : BorelSpace (GeneralLinear.upperUnipotent (r + 1) ℝ) := ⟨rfl⟩
local instance (r : ℕ) : MeasurableSpace (LeftUnipotentQuotient r ℝ) := borel _
local instance (r : ℕ) : BorelSpace (LeftUnipotentQuotient r ℝ) := ⟨rfl⟩

variable {r : ℕ}

def kernel (P : Langlands.GeneralLinear (r + 1) ℝ → ℂ)
    (Φ : (Fin (r + 1) → ℝ) → ℂ) (s : ℂ)
    (g : Langlands.GeneralLinear (r + 1) ℝ) : ℂ :=
  P g * Φ (lastRow g) * ArchimedeanLocal.detPower realNormalizedAbs g s

theorem detPower_unipotent_mul
    (u : GeneralLinear.upperUnipotent (r + 1) ℝ)
    (g : Langlands.GeneralLinear (r + 1) ℝ) (s : ℂ) :
    ArchimedeanLocal.detPower realNormalizedAbs (u.val * g) s = ArchimedeanLocal.detPower realNormalizedAbs g s := by
  simp only [ArchimedeanLocal.detPower, Units.val_mul, Matrix.det_mul, unipotent_det, one_mul]

theorem kernel_unipotent_mul (P : Langlands.GeneralLinear (r + 1) ℝ → ℂ)
    (hP : ∀ (u : GeneralLinear.upperUnipotent (r + 1) ℝ) g, P (u.val * g) = P g)
    (Φ : (Fin (r + 1) → ℝ) → ℂ) (s : ℂ)
    (u : GeneralLinear.upperUnipotent (r + 1) ℝ)
    (g : Langlands.GeneralLinear (r + 1) ℝ) :
    kernel P Φ s (u.val * g) = kernel P Φ s g := by
  simp only [kernel, hP, lastRow_unipotent_mul, detPower_unipotent_mul]

/-- Descent justifies changing the chosen representative after right translation. -/
theorem kernel_out_rightTranslate (P : Langlands.GeneralLinear (r + 1) ℝ → ℂ)
    (hP : ∀ (u : GeneralLinear.upperUnipotent (r + 1) ℝ) g, P (u.val * g) = P g)
    (Φ : (Fin (r + 1) → ℝ) → ℂ) (s : ℂ)
    (z : Langlands.GeneralLinear (r + 1) ℝ) (q : LeftUnipotentQuotient r ℝ) :
    kernel P Φ s ((QuotientIntegration.rightTranslate
        (GeneralLinear.upperUnipotent (r + 1) ℝ) z q).out) =
      kernel P Φ s (q.out * z) := by
  let f : LeftUnipotentQuotient r ℝ → ℂ :=
    QuotientIntegration.descend _ (kernel P Φ s) (kernel_unipotent_mul P hP Φ s)
  have hf (q : LeftUnipotentQuotient r ℝ) : kernel P Φ s q.out = f q :=
    congrArg f (Quotient.out_eq q)
  rw [hf]
  change f (QuotientIntegration.rightTranslate
    (GeneralLinear.upperUnipotent (r + 1) ℝ) z q) =
    f (Quotient.mk _ (q.out * z))
  rw [← QuotientIntegration.rightTranslate_mk, Quotient.out_eq]

theorem lastRow_mul_minusOne (g : Langlands.GeneralLinear (r + 1) ℝ) :
    lastRow (g * -1) = -lastRow g := by
  funext j
  change (g.val * (-1)) (Fin.last r) j = -g.val (Fin.last r) j
  simp

theorem detPower_mul_minusOne (g : Langlands.GeneralLinear (r + 1) ℝ) (s : ℂ) :
    ArchimedeanLocal.detPower realNormalizedAbs (g * -1) s = ArchimedeanLocal.detPower realNormalizedAbs g s := by
  unfold ArchimedeanLocal.detPower realNormalizedAbs
  congr 3
  congr 1
  change |Matrix.det (g.val * (-1))| = |Matrix.det g.val|
  simp [Matrix.det_neg, abs_mul]

theorem kernel_fourier_neg (P : Langlands.GeneralLinear (r + 1) ℝ → ℂ)
    (hP : ∀ (u : GeneralLinear.upperUnipotent (r + 1) ℝ) g, P (u.val * g) = P g)
    (k : ℂ) (hk : k ^ 2 = 1)
    (hPk : ∀ g, P (g * -1) = k * P g)
    (a : ℝˣ) (Φ : (Fin (r + 1) → ℝ) → ℂ) (s : ℂ)
    (q : LeftUnipotentQuotient r ℝ) :
    kernel P (realFourierTransform (-a) Φ) s q.out =
      k * kernel P (realFourierTransform a Φ) s
        ((QuotientIntegration.rightTranslate
          (GeneralLinear.upperUnipotent (r + 1) ℝ) (-1) q).out) := by
  rw [kernel_out_rightTranslate P hP]
  simp only [kernel, hPk, lastRow_mul_minusOne, detPower_mul_minusOne,
    RealJacquet.fourier_neg]
  calc
    _ = k ^ 2 * (P q.out * realFourierTransform a Φ (-lastRow q.out) *
        ArchimedeanLocal.detPower realNormalizedAbs q.out s) := by rw [hk, one_mul]
    _ = _ := by ring

theorem reflection (P : Langlands.GeneralLinear (r + 1) ℝ → ℂ)
    (hP : ∀ (u : GeneralLinear.upperUnipotent (r + 1) ℝ) g, P (u.val * g) = P g)
    (k : ℂ) (hk : k ^ 2 = 1)
    (hPk : ∀ g, P (g * -1) = k * P g)
    (a : ℝˣ) (D : RealQuotientMeasureData r)
    (Φ : (Fin (r + 1) → ℝ) → ℂ) (s : ℂ) :
    (Integrable (fun q : LeftUnipotentQuotient r ℝ =>
        kernel P (realFourierTransform (-a) Φ) s q.out) D.measure ↔
      Integrable (fun q : LeftUnipotentQuotient r ℝ =>
        kernel P (realFourierTransform a Φ) s q.out) D.measure) ∧
    (∫ q : LeftUnipotentQuotient r ℝ,
        kernel P (realFourierTransform (-a) Φ) s q.out ∂D.measure) =
      k * ∫ q : LeftUnipotentQuotient r ℝ,
        kernel P (realFourierTransform a Φ) s q.out ∂D.measure := by
  let : D.unipotentHaar.IsMulRightInvariant := D.unipotentHaar_rightInvariant
  let τ := QuotientIntegration.rightTranslate
    (GeneralLinear.upperUnipotent (r + 1) ℝ) (-1)
  have hτ : MeasurePreserving τ D.measure D.measure := D.compatible.right_invariant (-1)
  have hτemb : MeasurableEmbedding τ := τ.toMeasurableEquiv.measurableEmbedding
  have hkn : k ≠ 0 := by
    intro h
    rw [h, zero_pow (by decide)] at hk
    exact zero_ne_one hk
  have he : (fun q : LeftUnipotentQuotient r ℝ =>
      kernel P (realFourierTransform (-a) Φ) s q.out) =
      fun q : LeftUnipotentQuotient r ℝ =>
        k * kernel P (realFourierTransform a Φ) s (τ q).out := by
    funext q
    exact kernel_fourier_neg P hP k hk hPk a Φ s q
  constructor
  · rw [he, integrable_const_mul_iff (isUnit_iff_ne_zero.mpr hkn)]
    exact hτ.integrable_comp_emb hτemb
      (g := fun q : LeftUnipotentQuotient r ℝ =>
        kernel P (realFourierTransform a Φ) s q.out)
  · rw [he, integral_const_mul]
    congr 1
    exact hτ.integral_comp hτemb
      (fun q : LeftUnipotentQuotient r ℝ =>
        kernel P (realFourierTransform a Φ) s q.out)

end RealPlaceReflection

/-- The unitary adelic character in the target satisfies the existing standard predicate. -/
theorem RealPlaceReflection.unitary_isStandard (F : Type u) [Field F] [NumberField F]
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
    (hψ : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1) :
    IsStandardAdditiveCharacter F ψ.complex := by
  refine ⟨ψ.continuous_complex, fun h => ψ.nontrivial ?_, fun x => ?_, ψ.norm_complex⟩
  · ext x
    have hx := congrArg (fun χ : AddChar (Adeles F) ℂ => χ x) h
    simp only [HarmonicAnalysis.UnitaryAdditiveCharacter.complex_apply, AddChar.one_apply] at hx
    simpa using hx
  · rw [HarmonicAnalysis.UnitaryAdditiveCharacter.complex_apply, hψ x, Circle.coe_one]

/-- The formerly retained equal-rank reflection premise follows from actual actions
and the right invariance of the supplied quotient measure. -/
theorem realEqualDualReflection : RealEqualDualReflectionStatement.{u} := by
  intro F _ _ _ ψ hψ r T Td T' Td' hT hT' v a ha d d' dd dd' hd hd' hdd hdd'
    D W W' Φ hW hW'
  let P : Langlands.GeneralLinear (r + 1) ℝ → ℂ := fun g =>
    ArchimedeanLocal.dualFunction (r + 1) W g *
      ArchimedeanLocal.dualFunction (r + 1) W' g
  let k : ℂ := realMinusOneScalar T v * realMinusOneScalar T' v
  have hχ := RealPlaceReflection.unitary_isStandard F ψ hψ
  have hP : ∀ (u : GeneralLinear.upperUnipotent (r + 1) ℝ) g,
      P (u.val * g) = P g :=
    fun u g => hW.dual_product_unipotent_mul F hχ hW' u g
  have hk : k ^ 2 = 1 := by
    dsimp only [k]
    rw [mul_pow, realMinusOneScalar_sq, realMinusOneScalar_sq, one_mul]
  have hPk : ∀ g, P (g * -1) = k * P g := by
    intro g
    dsimp only [P, k]
    rw [hW.dual_mul_minusOne F, hW'.dual_mul_minusOne F]
    ring
  have hs (s : ℂ) := RealPlaceReflection.reflection P hP k hk hPk a D Φ s
  exact ⟨fun s => (hs s).1, fun s => (hs s).2⟩

/-- The real-place target now retains only the analytic restriction equation
and the parameter-determinant comparison. -/
def RealPlaceReflectionReductionStatement : Prop :=
  RealJacquetRestrictionEquationStatement.{u} →
  RealPairCentralCompatibilityStatement.{u} →
  RealPlaceFunctionalEquationStatement.{u}

theorem realPlaceReflectionReduction : RealPlaceReflectionReductionStatement.{u} := by
  intro hJ hC
  exact realPlaceJacquetConventionReduction hJ hC realEqualDualReflection

end Langlands.Global.RankinSelbergGlobal
