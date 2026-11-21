import Langlands.Global.AdelicBlockScalarParabolicDerivative

/-! # Compact curves and the actual scalar section Lie action -/

noncomputable section

open scoped Classical Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v

namespace Langlands.Global.AdelicBlockScalarSections

open Automorphic GeneralLinear PrimitiveAdelicHeight ArchimedeanGL

variable (F : Type u) [Field F] [NumberField F] {n : ℕ} (B : BlockShape n)
variable (S : ∀ i, OperatorRealization F (B.size i))

local notation "W" => smoothCompactFiniteSections F B S
local notation "e" => archimedeanGLCoordinates F n

private local instance : AddCommGroup (FiniteSmoothRealizedSections F B S) :=
  Submodule.addCommGroup _

/-- Scalar evaluation at one point of one fixed finite slice. -/
def smoothScalarSliceEvaluation (d : FiniteAdelicGL F n) (b : InfiniteAdelicGL F n) : W →ₗ[ℂ] ℂ :=
  (LinearMap.proj b).comp ((smoothFunctions F n).subtype.comp (smoothScalarSlice F B S d))

/-- Differentiating a scalar compact intertwiner along a genuine compact
curve gives intertwining in its real matrix direction. -/
theorem intertwines_sectionDifferential_of_compactCurve
    {V : Type v} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (standardInfiniteCompact F n) V)
    (J : ρ.IntertwiningMap (smoothCompactAction F B S))
    (X : RealLieAlgebra F n)
    (γ : ℝ → standardInfiniteCompact F n) (h₀ : γ 0 = 1)
    (hγ : HasDerivAt (fun t => compactMatrix F (γ t)) (realLieAlgebraToMatrix F n X) 0)
    (D : Module.End ℂ V)
    (hD : ∀ (x : V) (ℓ : V →ₗ[ℂ] ℂ), HasDerivAt (fun t => ℓ (ρ (γ t) x)) (ℓ (D x)) 0)
    (x : V) :
    J (D x) = sectionDifferential F B S X (J x) := by
  apply smoothScalarSlice_injective F B S
  funext d
  apply Subtype.ext
  funext b
  let ζ := (smoothScalarSliceEvaluation F B S d b).comp J.toLinearMap
  let β (t : ℝ) := b * (γ t).val
  have hb₀ : β 0 = b := by simp only [β, h₀, OneMemClass.coe_one, mul_one]
  have hb : HasDerivAt (fun t => (e (β t)).val)
      ((e b).val * realLieAlgebraToMatrix F n X) 0 := by
    simpa only [β, map_mul, Units.val_mul, compactMatrix] using hγ.const_mul (e b).val
  have hLeft := hD x ζ
  have hRight := hasDerivAt_smoothScalarSection_curve F B S (J x) d b X hb₀ hb
  have hEq (t : ℝ) :
      ζ (ρ (γ t) x) = (J x).val.val.val (AdelicGL.pair F n (β t) d) := by
    change (smoothScalarSlice F B S d (J (ρ (γ t) x))).val b = _
    rw [Representation.IntertwiningMap.isIntertwining _ _ J, smoothScalarSlice_compactAction]
    change (smoothScalarSlice F B S d (J x)).val (b * (γ t).val) = _
    rfl
  exact hLeft.unique (hRight.congr_of_eventuallyEq (Filter.Eventually.of_forall hEq))

end Langlands.Global.AdelicBlockScalarSections
