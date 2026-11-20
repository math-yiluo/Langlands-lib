import Langlands.Automorphic.CuspidalAdelicHilbertAction

/-! # The determinant-band identity for a supplied positive form -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 20000
set_option Elab.async false

namespace Langlands.Automorphic.OperatorDeterminantSlice

open Langlands.Global MeasureTheory
universe u
variable {F : Type u} [Field F] [NumberField F] {n : ℕ}

local instance bandFormRationalGroup : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance bandFormContinuousGroup : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance bandFormFiniteSmoothGroup : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance bandFormFormsGroup : AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance bandFormStableGroup : AddCommGroup (StableAutomorphicFunctions F n) :=
  Submodule.addCommGroup _
local instance bandFormSpaceGroup (S : OperatorRealization F n) : AddCommGroup S.Space :=
  Submodule.addCommGroup _

/-- A supplied form is computed by the canonical determinant-band integral. -/
def ComputesBandInnerProduct (S : OperatorRealization F n) (b : S.UnitaryForm) : Prop :=
  ∀ f g : S.Space, b.inner f g =
    ∫ q, Inner.inner ℂ (toQuotient F n S f q) (toQuotient F n S g q)
      ∂(quotientHaarMeasure F n).restrict (band F n)

end Langlands.Automorphic.OperatorDeterminantSlice
