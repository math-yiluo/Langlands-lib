import Langlands.Automorphic.OperatorUnitaryForm
import Langlands.Representation.Unitary.CompletionTransport

/-! # Hilbert equivalences induced by actual full-operator equivalences -/

noncomputable section
universe uF
set_option autoImplicit false
set_option maxHeartbeats 20000

namespace Langlands.Automorphic

open Langlands.Global

variable {F : Type uF} [Field F] [NumberField F] {n : ℕ}

local instance hilbertMapRationalGroup : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance hilbertMapContinuousGroup : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance hilbertMapSmoothGroup : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance hilbertMapFormsGroup : AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance hilbertMapStableGroup : AddCommGroup (StableAutomorphicFunctions F n) :=
  Submodule.addCommGroup _

namespace OperatorRealization

variable {S T : OperatorRealization F n}

local instance hilbertMapSourceGroup : AddCommGroup S.Space := Submodule.addCommGroup _
local instance hilbertMapTargetGroup : AddCommGroup T.Space := Submodule.addCommGroup _

namespace UnitaryForm

/-- An actual whole-operator equivalence induces a canonical Hilbert isometric
equivalence from the pullback of the target's supplied positive form. -/
def completedEquivalence (c : T.UnitaryForm) (e : S.Equivalence T) :
    (c.ofEquivalence e).finiteForm.HilbertCompletion ≃ₗᵢ[ℂ] c.finiteForm.HilbertCompletion :=
  (c.ofEquivalence e).finiteForm.completedEquiv c.finiteForm
    (Intertwiner.finiteRestriction e.toIntertwiningMap) (fun _ _ => rfl)
    e.toLinearEquiv.surjective

end UnitaryForm
end OperatorRealization
end Langlands.Automorphic
