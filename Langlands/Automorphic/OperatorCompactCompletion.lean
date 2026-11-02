import Langlands.Automorphic.OperatorUnitaryForm
import Langlands.Automorphic.OperatorCompactCompatibility
import Langlands.Representation.Unitary.EvaluationContinuity

/-! # Joint continuity of the completed actual compact action -/

noncomputable section
universe uF
set_option autoImplicit false

namespace Langlands.Automorphic

open Langlands.Global ContinuousRationalFunctions

variable {F : Type uF} [Field F] [NumberField F] {n : ℕ}

local instance compactCompletionRationalGroup : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance compactCompletionContinuousGroup : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance compactCompletionSmoothGroup : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance compactCompletionFormsGroup : AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance compactCompletionStableGroup : AddCommGroup (StableAutomorphicFunctions F n) :=
  Submodule.addCommGroup _

namespace OperatorRealization

variable (S : OperatorRealization F n)

local instance compactCompletionSpaceGroup : AddCommGroup S.Space := Submodule.addCommGroup _

/-- The faithful actual scalar functions carried by an operator realization. -/
def functionRealization : S.Space →ₗ[ℂ] (AdelicGL F n → ℂ) where
  toFun f := evaluate F n (S.toContinuous f)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem functionRealization_injective : Function.Injective S.functionRealization := by
  intro f g h
  apply S.toContinuous_injective
  apply Subtype.ext
  apply Subtype.ext
  exact h

/-- Each scalar evaluation of an actual compact orbit is continuous. -/
theorem continuous_functionRealization_compactOrbit (f : S.Space) (x : AdelicGL F n) :
    Continuous (fun k : standardInfiniteCompact F n =>
      S.functionRealization (S.compactRepresentation k f) x) := by
  change Continuous (fun k : standardInfiniteCompact F n =>
    evaluate F n (S.toContinuous (S.compactRepresentation k f)) x)
  simp_rw [S.evaluate_compactRepresentation]
  exact (continuous_evaluate F n (S.toContinuous f)).comp
    (continuous_const.mul ((AdelicGL.ofInfinite F n).continuous.comp continuous_subtype_val))

namespace UnitaryForm

variable {S}

/-- The actual completed compact action, jointly continuous on the completion
of the same single positive form used by finite translation. -/
def completedCompactContinuousAction (b : S.UnitaryForm) :
    C(standardInfiniteCompact F n × b.finiteForm.HilbertCompletion,
      b.finiteForm.HilbertCompletion) :=
  b.compactForm.completedContinuousActionOfFiniteEvaluations
    S.functionRealization S.functionRealization_injective
    S.compactRepresentation_isFiniteVector S.continuous_functionRealization_compactOrbit

end UnitaryForm
end OperatorRealization
end Langlands.Automorphic
