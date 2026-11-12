import Langlands.HarmonicAnalysis.GroupAction
import Langlands.HarmonicAnalysis.PointwiseTestAlgebraCore
import Mathlib.MeasureTheory.Group.ModularCharacter
import Mathlib.MeasureTheory.Measure.Haar.MulEquivHaarChar

/-! # Renard II.3.6–II.3.8: integration distributions and conventions -/

noncomputable section

open MeasureTheory
open scoped NNReal

namespace Langlands.HarmonicAnalysis.Distribution

universe uX uG

variable {X : Type uX} [TopologicalSpace X]

/-- Renard's real-valued nonnegative test functions, on the existing complex carrier. -/
def IsNonnegativeTest (f : SchwartzBruhat X) : Prop :=
  ∀ x, (f x).im = 0 ∧ 0 ≤ (f x).re

/-- Strict positivity on every nonzero real-valued nonnegative test. -/
def IsPositive (D : Distribution X) : Prop :=
  ∀ f : SchwartzBruhat X, f ≠ 0 → IsNonnegativeTest f →
    (D f).im = 0 ∧ 0 < (D f).re

/-- The existing pointwise smooth multiplier, transported along the published
identity-on-values equivalence with scalar tests. -/
def multiplyTest (f : LocallyConstant X ℂ) : Module.End ℂ (SchwartzBruhat X) :=
  PointwiseTestAlgebra.scalarEquiv.toLinearMap.comp
    ((PointwiseTestAlgebra.multiplier f).comp
      PointwiseTestAlgebra.scalarEquiv.symm.toLinearMap)

@[simp]
theorem multiplyTest_apply (f : LocallyConstant X ℂ) (φ : SchwartzBruhat X) (x : X) :
    multiplyTest f φ x = f x * φ x := rfl

section Integration

variable [MeasurableSpace X] [BorelSpace X]
variable (μ : Measure X) [IsFiniteMeasureOnCompacts μ]

theorem test_integrable (f : SchwartzBruhat X) : Integrable (f : X → ℂ) μ :=
  f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport

/-- The actual integration functional, not an abstractly supplied distribution. -/
def ofMeasure : Distribution X where
  toFun f := ∫ x, f x ∂μ
  map_add' f g := integral_add (test_integrable μ f) (test_integrable μ g)
  map_smul' c _f := integral_smul c _

@[simp]
theorem ofMeasure_apply (f : SchwartzBruhat X) :
    ofMeasure μ f = ∫ x, f x ∂μ := rfl

/-- The source map `f ↦ f μ`, with its actual integral and complex linearity. -/
def density : LocallyConstant X ℂ →ₗ[ℂ] Distribution X where
  toFun f := (ofMeasure μ).comp (multiplyTest f)
  map_add' f g := by
    ext φ
    change ofMeasure μ (multiplyTest (f + g) φ) = _
    have h : multiplyTest (f + g) φ = multiplyTest f φ + multiplyTest g φ := by
      ext x
      exact add_mul (f x) (g x) (φ x)
    rw [h, map_add]
    rfl
  map_smul' c f := by
    ext φ
    change ofMeasure μ (multiplyTest (c • f) φ) = _
    have h : multiplyTest (c • f) φ = c • multiplyTest f φ := by
      ext x
      exact mul_assoc c (f x) (φ x)
    rw [h, map_smul]
    rfl

@[simp]
theorem density_apply (f : LocallyConstant X ℂ) (φ : SchwartzBruhat X) :
    density μ f φ = ∫ x, f x * φ x ∂μ := rfl

theorem density_one : density μ 1 = ofMeasure μ := by
  ext φ
  simp [density_apply, ofMeasure_apply]

/-- Restriction of the same density map to the original scalar tests. -/
def testDensity : SchwartzBruhat X →ₗ[ℂ] Distribution X :=
  (density μ).comp
    ({ toFun := fun f => ⟨(f : X → ℂ), f.locallyConstant⟩
       map_add' := fun _ _ => rfl
       map_smul' := fun _ _ => rfl } :
      SchwartzBruhat X →ₗ[ℂ] LocallyConstant X ℂ)

@[simp]
theorem testDensity_apply (f φ : SchwartzBruhat X) :
    testDensity μ f φ = ∫ x, f x * φ x ∂μ := rfl

end Integration

section Groups

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

def IsLeftInvariant (D : Distribution G) : Prop :=
  ∀ g : G, GroupAction.leftDistributions g D = D

def IsRightInvariant (D : Distribution G) : Prop :=
  ∀ g : G, GroupAction.rightDistributions g D = D

variable [LocallyCompactSpace G]

/-- Exact reciprocal bridge to Mathlib's modular character.
Renard uses `r(g) μ = δ(g) μ`, where the point action is `x ↦ x g⁻¹`. -/
def renardModular : G →* ℝ≥0 where
  toFun g := Measure.modularCharacter g⁻¹
  map_one' := by simp
  map_mul' g h := by simp [mul_comm]

@[simp]
theorem renardModular_apply (g : G) :
    renardModular g = Measure.modularCharacter g⁻¹ := rfl

theorem renardModular_eq_inv (g : G) :
    renardModular g = (Measure.modularCharacter g)⁻¹ := by
  symm
  apply inv_eq_of_mul_eq_one_right
  change Measure.modularCharacter g * Measure.modularCharacter g⁻¹ = 1
  rw [← map_mul, mul_inv_cancel, map_one]

variable [MeasurableSpace G] [BorelSpace G]

/-- Renard's automorphism module is likewise the reciprocal of Mathlib's
image-scaling character: it scales pushforward, not image volumes. -/
def renardAutomorphismModule (σ : G ≃ₜ* G) : ℝ≥0 :=
  (mulEquivHaarChar σ)⁻¹

end Groups

end Langlands.HarmonicAnalysis.Distribution
