import Langlands.TraceFormula.NormOneLeviInduction
import Langlands.TraceFormula.CyclicSplitCenterMeasureStatement
import Langlands.Global.AdelicGLStandardCompact
import Langlands.Global.AdelicGLTransport
import Langlands.Global.AdelicGroupPolish
import Langlands.Representation.Unitary.IntegratedOperator

/-! # Right translation and arithmetic pullback on discrete Levi induction -/

noncomputable section

open MeasureTheory
open scoped CategoryTheory.MonObj NNReal

set_option autoImplicit false
set_option maxHeartbeats 2500000

namespace Langlands.TraceFormula.NormOneLeviInduction

open Langlands.Global Langlands.Global.AdelicGroupPoints
open scoped CoordinateLevi.Presentation

variable {F : Type} [Field F] [NumberField F] {n : ℕ} {L : CoordinateLevi n}
variable {P : L.Presentation} (D : Model F P) (V : Submodule ℂ (LeviL2 F P)) (t : ℝ)

instance : CompleteSpace (D.hilbertSliceWithSupport V t) :=
  (Submodule.isClosed_topologicalClosure _).completeSpace_coe

/-- The standard adelic compact and a continuous compactly supported cutoff of mass one. -/
def Model.IsStandardCompactPicture : Prop :=
  D.compact = (PrimitiveAdelicHeight.standardCompact F n).comap
      (GeneralLinearGroupPoints.adelicHomeomorph F n).toMonoidHom ∧
    Continuous D.cutoff ∧ HasCompactSupport D.cutoff

/-- A strongly continuous unitary action on the Hilbert slice, extended to the full adelic
points by taking the positive split centre to act trivially. -/
structure RightAction where
  toHom : AdelicGroupPoints F (cyclicBaseGroup F n) →*
    (D.hilbertSliceWithSupport V t →L[ℂ] D.hilbertSliceWithSupport V t)
  norm_apply (x : AdelicGroupPoints F (cyclicBaseGroup F n)) (v : D.hilbertSliceWithSupport V t) :
    ‖toHom x v‖ = ‖v‖
  continuous_apply (v : D.hilbertSliceWithSupport V t) : Continuous (fun x => toHom x v)
  positiveScalar (a : ℝ≥0ˣ) :
    toHom ((GeneralLinearGroupPoints.adelicHomeomorph F n).symm (adelicPositiveScalar F n a)) = 1

variable {D V t}

/-- The action lifts actual right translation on represented sections. -/
def RightAction.IsInduced (π : RightAction D V t) : Prop :=
  ∀ (x : AdelicGroupPoints F (cyclicBaseGroup F n)) (v : D.hilbertSliceWithSupport V t) φ,
    D.IsSectionWithSupport V φ → HasImaginaryInfinitesimalNorm F n φ t → D.Represents v.val φ →
    D.Represents (π.toHom x v).val (fun g => φ (g * x))

/-- The integrated zero-parameter action of an integrable test on the actual norm-one group. -/
def RightAction.integrated (π : RightAction D V t)
    (ν : Measure (normOneSubgroup F (cyclicBaseGroup F n)))
    (f : normOneSubgroup F (cyclicBaseGroup F n) → ℂ) (hf : Integrable f ν) :
    D.hilbertSliceWithSupport V t →L[ℂ] D.hilbertSliceWithSupport V t :=
  Langlands.Analysis.integratedIsometricAction ν (π.toHom.comp (normOneSubgroup F _).subtype)
    (fun x v => π.norm_apply x.val v)
    (fun v => ((π.continuous_apply v).comp continuous_subtype_val).aestronglyMeasurable) f hf

/-- Arithmetic transport of the actual adelic group-scheme points, in matrix coordinates. -/
def adelicFieldAutomorphism (F : Type) [Field F] [NumberField F] (n : ℕ) (σ : F ≃+* F) :
    AdelicGroupPoints F (cyclicBaseGroup F n) ≃ₜ* AdelicGroupPoints F (cyclicBaseGroup F n) :=
  let e := GeneralLinearGroupPoints.adelicHomeomorph F n
  e.trans ((AdelicGLTransport.adelicEquiv n σ).trans e.symm)

/-- The arithmetic twist on represented sections is pullback by the inverse automorphism. -/
def RightAction.IsGaloisPullback (π : RightAction D V t) (σ : F ≃+* F)
    (T : D.hilbertSliceWithSupport V t ≃ₗᵢ[ℂ] D.hilbertSliceWithSupport V t) : Prop :=
  (∀ (v : D.hilbertSliceWithSupport V t) φ, D.IsSectionWithSupport V φ →
    HasImaginaryInfinitesimalNorm F n φ t → D.Represents v.val φ →
    D.Represents (T v).val (φ ∘ (adelicFieldAutomorphism F n σ).symm)) ∧
  ∀ (x : AdelicGroupPoints F (cyclicBaseGroup F n)) (v : D.hilbertSliceWithSupport V t),
    T (π.toHom x v) = π.toHom (adelicFieldAutomorphism F n σ x) (T v)

/-- Existence of the actual zero-parameter right action on the induced Hilbert slices. -/
def CyclicInducedRightActionStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (n : ℕ), 0 < n →
    ∀ (L : CoordinateLevi n) (P : L.Presentation) (D : Model F P), D.IsStandardCompactPicture →
    ∀ (V : Submodule ℂ (LeviL2 F P)), V ≤ D.leviDiscrete → IsClosed (V : Set (LeviL2 F P)) →
    ∀ t : ℝ, 0 ≤ t → ∃ π : RightAction D V t, π.IsInduced

/-- Existence of arithmetic pullback on the full discrete inducing space. -/
def CyclicInducedGaloisPullbackStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (n : ℕ), 0 < n →
    ∀ (σ : F ≃+* F), IsOfFinOrder σ →
    ∀ (L : CoordinateLevi n) (P : L.Presentation) (D : Model F P), D.IsStandardCompactPicture →
    ∀ t : ℝ, 0 ≤ t → ∀ π : RightAction D D.leviDiscrete t, π.IsInduced →
    ∃ T : D.hilbertSlice t ≃ₗᵢ[ℂ] D.hilbertSlice t, π.IsGaloisPullback σ T

end Langlands.TraceFormula.NormOneLeviInduction
