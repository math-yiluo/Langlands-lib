import Langlands.Automorphic.CuspidalHilbertIntertwinerCore
import Langlands.Automorphic.CuspidalHilbertCoefficientLifts
import Langlands.Automorphic.CuspidalHilbertBandForm

/-! # The actual adelic completion and its operator comparisons -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 20000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic

open Langlands.Global
open scoped NumberField
universe u
variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] {r : ℕ}

local instance adelicCompletionRationalGroup (n : ℕ) : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance adelicCompletionContinuousGroup (n : ℕ) : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance adelicCompletionFiniteSmoothGroup (n : ℕ) : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance adelicCompletionFormsGroup (n : ℕ) : AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance adelicCompletionStableGroup (n : ℕ) : AddCommGroup (StableAutomorphicFunctions F n) :=
  Submodule.addCommGroup _
local instance adelicCompletionSpaceGroup (S : OperatorRealization F (r + 1)) : AddCommGroup S.Space :=
  Submodule.addCommGroup _

namespace OperatorDeterminantSlice

/-- The reconstructed action with its coefficient lifts and both original
bounded-operator comparisons on the completion of the supplied form. -/
def adelicCompletion (T : CuspidalOperatorRealization F r)
    (χ : NumberField.IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ)
    (hχ : ∀ z, ‖(χ z : ℂ)‖ = 1) (hTχ : T.realization.HasCentralCharacter χ)
    (b : T.realization.UnitaryForm) (hb : ComputesBandInnerProduct T.realization b) :
    OperatorUnitaryFormCore.AdelicCompletion b where
  action := adelicHilbertRepresentation T cuspidalHilbertOrbitCoefficient χ hχ hTχ b hb
  differential a v := T.realization.envelopingAction a v
  coefficients := adelicHilbertRepresentation_jointFiniteCoefficientLifts T χ hχ hTχ b hb
  boundedCompatibility :=
    adelicHilbertRepresentation_boundedCompatibility T cuspidalHilbertOrbitCoefficient χ hχ hTχ b hb

end OperatorDeterminantSlice
end Langlands.Automorphic
