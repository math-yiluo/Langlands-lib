import Langlands.Automorphic.CuspidalHilbertCoefficientComparison
import Langlands.Automorphic.CuspidalHilbertOrbitCoefficientProof
import Langlands.Automorphic.CuspidalHilbertSmoothEmbedding

/-! # Joint-finite coefficients of the original cuspidal Hilbert action -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 20000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic

open Langlands.Global MeasureTheory
open scoped NumberField
universe u
variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] {r : ℕ}

local instance rationalGroup (n : ℕ) : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance continuousGroup (n : ℕ) : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance finiteSmoothGroup (n : ℕ) : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance formsGroup (n : ℕ) : AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance stableGroup (n : ℕ) : AddCommGroup (StableAutomorphicFunctions F n) :=
  Submodule.addCommGroup _
local instance spaceGroup (S : OperatorRealization F (r + 1)) : AddCommGroup S.Space :=
  Submodule.addCommGroup _

namespace OperatorDeterminantSlice

variable (T : CuspidalOperatorRealization F r)
  (χ : NumberField.IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ)
  (hχ : ∀ z, ‖(χ z : ℂ)‖ = 1) (hTχ : T.realization.HasCentralCharacter χ)
  (b : T.realization.UnitaryForm)
  (hb : ∀ f g : T.Space, b.inner f g =
    ∫ q, Inner.inner ℂ (toQuotient F (r + 1) T.realization f q)
      (toQuotient F (r + 1) T.realization g q)
      ∂(quotientHaarMeasure F (r + 1)).restrict (band F (r + 1)))

/-- The scalar formula for the reconstructed action gives its joint-finite
coefficient lifts with the original genuine enveloping action. -/
theorem adelicHilbertRepresentation_jointFiniteCoefficientLifts :
    HilbertCoefficientComparison.JointFiniteCoefficientLifts
      (adelicHilbertRepresentation T cuspidalHilbertOrbitCoefficient χ hχ hTχ b hb)
      (AdelicGL.ofInfinite F (r + 1)) b.finiteForm.toHilbert
      (fun a v => T.realization.envelopingAction a v) := by
  let J := translatedHilbertEmbedding T.realization T.cuspidal (Nat.succ_ne_zero r) χ hχ hTχ b hb
  let U := adelicHilbertRepresentation T cuspidalHilbertOrbitCoefficient χ hχ hTχ b hb
  refine HilbertCoefficientComparison.jointFiniteCoefficientLifts_of_values
    U (AdelicGL.ofInfinite F (r + 1)) b.finiteForm.toHilbert
    (fun a v => T.realization.envelopingAction a v) (J 1)
    (CuspidalHilbertOrbitCoefficient.coefficient T) ?_ ?_
  · intro w v g
    exact (Langlands.UnitaryEmbeddingFamily.inner_dense_orbit J U
      (adelicHilbertRepresentation_realizes T cuspidalHilbertOrbitCoefficient χ hχ hTχ b hb)
      b.finiteForm.toHilbert (fun a f => translatedToL2 T.realization T.cuspidal a f)
      (translatedHilbertEmbedding_toHilbert T.realization T.cuspidal (Nat.succ_ne_zero r)
        χ hχ hTχ b hb) w v (AdelicGL.ofInfinite F (r + 1) g)).trans
      (inner_translatedToL2_left T (J 1 w) (AdelicGL.ofInfinite F (r + 1) g) v)
  · intro w
    exact (cuspidalHilbertOrbitCoefficient F r T ⟨χ, hχ, hTχ⟩ w).2

end OperatorDeterminantSlice
end Langlands.Automorphic
