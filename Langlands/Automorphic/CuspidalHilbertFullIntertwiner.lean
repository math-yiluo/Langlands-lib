import Langlands.Automorphic.CuspidalHilbertAdelicCompletion
import Langlands.Automorphic.CuspidalJointAdmissibility

/-! # Full adelic covariance of the original Hilbert extensions -/

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

local instance fullIntertwinerRationalGroup (n : ℕ) : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance fullIntertwinerContinuousGroup (n : ℕ) : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance fullIntertwinerFiniteSmoothGroup (n : ℕ) : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance fullIntertwinerFormsGroup (n : ℕ) : AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance fullIntertwinerStableGroup (n : ℕ) : AddCommGroup (StableAutomorphicFunctions F n) :=
  Submodule.addCommGroup _
local instance fullIntertwinerSpaceGroup (S : OperatorRealization F (r + 1)) : AddCommGroup S.Space :=
  Submodule.addCommGroup _

open OperatorDeterminantSlice

/-- Actual operator equivalences extend to the two independent completions with
full adelic covariance and a positive ratio, for the specified band forms. -/
def CuspidalHilbertFullIntertwinerStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (r : ℕ) (S T : CuspidalOperatorRealization F r)
    (χS χT : NumberField.IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ)
    (hχS : ∀ z, ‖(χS z : ℂ)‖ = 1) (hχT : ∀ z, ‖(χT z : ℂ)‖ = 1)
    (hSχ : S.realization.HasCentralCharacter χS) (hTχ : T.realization.HasCentralCharacter χT)
    (b : S.realization.UnitaryForm) (c : T.realization.UnitaryForm)
    (hb : OperatorDeterminantSlice.ComputesBandInnerProduct S.realization b)
    (hc : OperatorDeterminantSlice.ComputesBandInnerProduct T.realization c)
    (e : S.Equivalence T),
    OperatorUnitaryFormCore.AdelicHilbertFormComparison b c
      (adelicCompletion S χS hχS hSχ b hb).action (adelicCompletion T χT hχT hTχ c hc).action e

theorem cuspidalHilbertFullIntertwiner : CuspidalHilbertFullIntertwinerStatement.{u} := by
  intro F _ _ _ r S T χS χT hχS hχT hSχ hTχ b c hb hc e
  exact OperatorUnitaryFormCore.AdelicCompletion.formComparison b c
    (adelicCompletion S χS hχS hSχ b hb) (adelicCompletion T χT hχT hTχ c hc) e
    (OperatorRealization.UnitaryForm.exists_hilbertEquivalence b c e S.irreducible S.isJointlyAdmissible)
    (OperatorRealization.Intertwiner.differential e.toIntertwiningMap)
    (OperatorRealization.Intertwiner.compact e.toIntertwiningMap)
    (OperatorRealization.Intertwiner.finite e.toIntertwiningMap)

end Langlands.Automorphic
