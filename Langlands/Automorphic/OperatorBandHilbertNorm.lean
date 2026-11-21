import Langlands.Automorphic.CuspidalHilbertBandForm

/-! # Equality of the form norm and the determinant-band L² norm -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000

namespace Langlands.Automorphic.OperatorDeterminantSlice

open Langlands.Global MeasureTheory

universe u

variable {F : Type u} [Field F] [NumberField F] {n : ℕ} (S : OperatorRealization F n)

local instance bandNormRationalGroup : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance bandNormContinuousGroup : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance bandNormSmoothGroup : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance bandNormFormsGroup : AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance bandNormStableGroup : AddCommGroup (StableAutomorphicFunctions F n) :=
  Submodule.addCommGroup _
local instance bandNormSpaceGroup : AddCommGroup S.Space := Submodule.addCommGroup _

/-- The norm of an original vector in the supplied completion is its
actual determinant-band L² norm when the form is computed on that band. -/
theorem norm_toL2_eq_toHilbert (b : S.UnitaryForm) (hb : ComputesBandInnerProduct S b)
    (hL2 : ∀ x : S.Space, MemLp (toQuotient F n S x) 2
      ((quotientHaarMeasure F n).restrict (band F n))) (w : S.Space) :
    ‖toL2 F n S (quotientHaarMeasure F n) hL2 w‖ = ‖b.finiteForm.toHilbert w‖ := by
  let z := toL2 F n S (quotientHaarMeasure F n) hL2 w
  have he : Inner.inner ℂ z z = b.inner w w :=
    (inner_toL2 F n S (quotientHaarMeasure F n) hL2 w w).trans (hb w w).symm
  exact (norm_eq_sqrt_re_inner (𝕜 := ℂ) z).trans
    ((congrArg (fun s : ℂ => Real.sqrt s.re) he).trans (b.norm_toHilbert w).symm)

end Langlands.Automorphic.OperatorDeterminantSlice
