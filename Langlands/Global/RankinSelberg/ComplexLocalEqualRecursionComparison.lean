import Langlands.Global.RankinSelberg.ComplexLocalEqualRecursionNormalization
import Langlands.Representation.GodementJacquet.ComplexJacquetRecursion

/-! # The full unipotent and rectangular recursions for Schwartz tests -/

noncomputable section

open MeasureTheory
open Langlands.GeneralLinear Langlands.GodementJacquet
open scoped Matrix.Norms.Elementwise NNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexJacquet

open ArchimedeanLocal

attribute [local instance] archimedeanEquationComplexGLMeasurable
  archimedeanEquationComplexGLBorel archimedeanEquationComplexNMeasurable
  archimedeanEquationComplexNBorel archimedeanEquationComplexQMeasurable
  archimedeanEquationComplexQBorel

variable {r : ℕ}

local notation "m" => r + 1
local notation "n" => (r + 1) + 1
local notation "H" => Langlands.GeneralLinear m ℂ
local notation "G" => Langlands.GeneralLinear n ℂ
local notation "N" => GeneralLinear.upperUnipotent m ℂ
local notation "Col" => Fin m → ℂ
local notation "Rect" => Matrix (Fin m) (Fin n) ℂ

private theorem equalRectangleKernel_eq (b : ℂˣ) (f : Rect → ℂ) (p : N × Col) :
    complexEqualRectangleKernel b f p = complexJacquetRectangleKernel b f p := by
  unfold complexEqualRectangleKernel complexJacquetRectangleKernel
  rw [traceCharacter_add, mul_comm (traceCharacter b (p.2 (Fin.last r)))]
  rfl

private theorem integrable_equalRectangleKernel (D₁ : ComplexQuotientMeasureData r) (b : ℂˣ)
    (Φ : SchwartzMap Rect ℂ) (k : H) (g : G) :
    Integrable (complexEqualRectangleKernel (-b) (fun X => Φ ((k⁻¹).val * X * g.val)))
      (D₁.unipotentHaar.prod (complexCoordinateMeasure (Fin m) (-b))) := by
  let : D₁.unipotentHaar.IsHaarMeasure := D₁.unipotentHaar_isHaar
  let w := weylLong n ℂ
  let Ψ := complexRectangularTranslate k⁻¹ (w * g) Φ
  have htest (X : Rect) : Ψ (X * w.val) = Φ ((k⁻¹).val * X * g.val) := by
    dsimp only [Ψ]
    simp only [complexRectangularTranslate_apply, Units.val_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc w.val w.val g.val, ← Units.val_mul,
      weylLong_mul_self, Units.val_one, Matrix.one_mul]
  have h := (integral_complexJacquetRectangle_unipotent b Ψ D₁.unipotentHaar).1
  change Integrable (complexJacquetRectangleKernel (-b) (fun X => Ψ (X * w.val)))
    (D₁.unipotentHaar.prod (complexCoordinateMeasure (Fin m) b)) at h
  simp_rw [htest] at h
  change Integrable (fun p => complexEqualRectangleKernel (-b)
    (fun X => Φ ((k⁻¹).val * X * g.val)) p) _
  simpa only [equalRectangleKernel_eq, complexCoordinateMeasure, complexSelfDualMeasure_neg_scale]
    using h

/-- The two complex Jacquet recursions agree up to a common positive scalar
for every Schwartz test of the rectangular variables. -/
def ComplexLocalEqualRecursionComparisonStatement : Prop :=
  ∀ (D : ComplexQuotientMeasureData (r + 1)) (D₁ : ComplexQuotientMeasureData r) (a : ℂˣ),
  ∃ c : ℝ≥0, 0 < c ∧
  ∀ (b : ℂˣ), complexSelfDualMeasure b = complexSelfDualMeasure a →
  ∀ (η : ℂˣ →* ℂˣ) (Φ : SchwartzMap Rect ℂ) (U : H → ℂ) (g : G),
    complexEqualUnipotentRecursion D D₁ η b Φ U g =
      (c : ℂ) * complexJacquetRecursion b D₁ Φ U η g

theorem complexLocalEqualRecursionComparison :
    ComplexLocalEqualRecursionComparisonStatement (r := r) := by
  intro D D₁ a
  obtain ⟨c, hc, hrec⟩ := complexLocalEqualRecursionNormalization (r := r) D D₁ a
  refine ⟨c, hc, fun b hb η Φ U g => ?_⟩
  rw [hrec b hb η Φ U g (fun k => integrable_equalRectangleKernel D₁ b Φ k g)]
  unfold complexJacquetRecursion complexJacquetRecursionKernel complexJacquetDetWeight
    complexJacquetUnipotentAverage
  simp only [equalRectangleKernel_eq, ← mul_assoc, ← integral_const_mul]
  rfl

end Langlands.Global.RankinSelbergGlobal.ComplexJacquet
