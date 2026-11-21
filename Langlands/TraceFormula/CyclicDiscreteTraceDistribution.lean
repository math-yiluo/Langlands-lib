import Langlands.TraceFormula.CyclicZeroIntertwinerStatement
import Langlands.Analysis.OperatorTrace

/-! # The discrete trace sum on the actual norm-one general linear group -/

noncomputable section

open MeasureTheory
open scoped CategoryTheory.MonObj BigOperators

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

namespace Langlands.TraceFormula

open Langlands.Global Langlands.Global.AdelicGroupPoints
open Langlands.Analysis.OperatorIdeals NormOneLeviInduction
open scoped CoordinateLevi.Presentation

/-- The norm-one test space is spanned by restrictions of the compactly supported smooth
adelic tests with finite left and right infinite compact types. -/
def normOneTraceTestSpace (F : Type) [Field F] [NumberField F] (n : ℕ) :
    Submodule ℂ (normOneSubgroup F (cyclicBaseGroup F n) → ℂ) :=
  Submodule.span ℂ {f | ∃ h : AdelicGroupPoints F (cyclicBaseGroup F n) → ℂ,
    IsCyclicTraceTest F (AdelicGL F n) (GeneralLinearGroupPoints.adelicHomeomorph F n)
      (adelicInfiniteStandardCompact F n) h ∧ f = fun x => h x.val}

/-- The order of the operators in a discrete trace summand. The supplied twist can be the
identity, an arithmetic pullback, or a twist on a supported induction. -/
def discreteTraceOperator {F : Type} [Field F] [NumberField F] {n : ℕ} {L : CoordinateLevi n}
    {P : L.Presentation} {D : Model F P} {V : Submodule ℂ (LeviL2 F P)} {t : ℝ}
    (π : RightAction D V t)
    (intertwiner twist : D.hilbertSliceWithSupport V t →L[ℂ] D.hilbertSliceWithSupport V t)
    (ν : Measure (normOneSubgroup F (cyclicBaseGroup F n)))
    (f : normOneSubgroup F (cyclicBaseGroup F n) → ℂ) (hf : Integrable f ν) :
    D.hilbertSliceWithSupport V t →L[ℂ] D.hilbertSliceWithSupport V t :=
  intertwiner.comp (twist.comp (π.integrated ν f hf))

/-- The operators on the full discrete induction for every Levi and regular Weyl element. -/
structure DiscreteTraceData (F : Type) [Field F] [NumberField F] (n : ℕ) (t : ℝ) where
  presentation (L : CoordinateLevi n) : L.Presentation
  inductionModel (L : CoordinateLevi n) : Model F (presentation L)
  action (L : CoordinateLevi n) : RightAction (inductionModel L) (inductionModel L).leviDiscrete t
  intertwiner (L : CoordinateLevi n) (s : CoordinateLevi.Presentation.RegularWeyl L) :
    (inductionModel L).hilbertSlice t →L[ℂ] (inductionModel L).hilbertSlice t
  twist (L : CoordinateLevi n) :
    (inductionModel L).hilbertSlice t →L[ℂ] (inductionModel L).hilbertSlice t

namespace DiscreteTraceData

variable {F : Type} [Field F] [NumberField F] {n : ℕ} {t : ℝ} (D : DiscreteTraceData F n t)

/-- The compact picture, the right action and the intertwining operators have their
specified geometric and analytic realizations. -/
def IsSpectral : Prop :=
  ∀ L : CoordinateLevi n,
    (D.inductionModel L).IsStandardCompactPicture ∧ (D.action L).IsInduced ∧
    ∀ s, IsRegularZeroIntertwiner (D.inductionModel L) s t (D.intertwiner L s)

/-- Ordinary trace data use the identity twist. -/
def IsOrdinary : Prop := ∀ L : CoordinateLevi n, D.twist L = 1

/-- Twisted trace data use inverse arithmetic pullback on the represented sections. -/
def IsArithmetic (σ : F ≃+* F) : Prop :=
  ∀ L : CoordinateLevi n,
    ∃ T : (D.inductionModel L).hilbertSlice t ≃ₗᵢ[ℂ] (D.inductionModel L).hilbertSlice t,
      (D.action L).IsGaloisPullback σ T ∧ D.twist L = T.toContinuousLinearEquiv.toContinuousLinearMap

variable (ν : Measure (normOneSubgroup F (cyclicBaseGroup F n)))
variable (f : normOneSubgroup F (cyclicBaseGroup F n) → ℂ) (hf : Integrable f ν)

/-- The operator whose trace contributes at a specified Levi and regular Weyl element. -/
def summand (L : CoordinateLevi n) (s : CoordinateLevi.Presentation.RegularWeyl L) :
    (D.inductionModel L).hilbertSlice t →L[ℂ] (D.inductionModel L).hilbertSlice t :=
  discreteTraceOperator (D.action L) (D.intertwiner L s) (D.twist L) ν f hf

/-- The discrete trace sum with the Levi Weyl ratio and the reciprocal regular determinant. -/
def normOneTrace : ℂ := by
  classical
  exact ∑ L : CoordinateLevi n, ∑ s : CoordinateLevi.Presentation.RegularWeyl L,
    (L.discreteWeight s.val : ℂ) * operatorTrace (D.summand ν f hf L s)

/-- Each summand on the norm-one test space is trace class, and the trace sum gives
a complex-linear distribution on that space. -/
def HasNormOneDistribution : Prop :=
  ∃ h : ∀ g : normOneTraceTestSpace F n, Integrable g.val ν,
    (∀ g L s, IsTraceClass (D.summand ν g.val (h g) L s)) ∧
      ∃ I : normOneTraceTestSpace F n →ₗ[ℂ] ℂ,
        ∀ g, I g = D.normOneTrace ν g.val (h g)

end DiscreteTraceData

/-- Spectral data exist on the ordinary side and on a finite-order arithmetic component. -/
def CyclicDiscreteTraceDataStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (n : ℕ), 0 < n → ∀ t : ℝ, 0 ≤ t →
    (∃ D : DiscreteTraceData F n t, D.IsSpectral ∧ D.IsOrdinary) ∧
    ∀ (σ : F ≃+* F), IsOfFinOrder σ →
      ∃ D : DiscreteTraceData F n t, D.IsSpectral ∧ D.IsArithmetic σ

/-- Trace class and linearity on the norm-one test space for the discrete trace sum. -/
def CyclicNormOneTraceClassStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (n : ℕ), 0 < n → ∀ t : ℝ, 0 ≤ t →
    ∀ (D : DiscreteTraceData F n t), D.IsSpectral →
    ∀ (ν : Measure (normOneSubgroup F (cyclicBaseGroup F n))) [ν.IsHaarMeasure],
      D.HasNormOneDistribution ν

end Langlands.TraceFormula
