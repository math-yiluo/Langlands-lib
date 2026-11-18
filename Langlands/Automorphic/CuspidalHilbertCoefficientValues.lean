import Langlands.Automorphic.CuspidalHilbertSmoothEmbedding

/-! # Genuine real generators of the conditional actual Hilbert action -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 20000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
open scoped Classical Manifold ContDiff

namespace Langlands.Automorphic
open Langlands.Global MeasureTheory
open scoped NumberField Matrix.Norms.Operator
universe u
variable {F : Type u} [Field F] [NumberField F] {n : ℕ}

local instance hilbertGeneratorRationalGroup : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance hilbertGeneratorContinuousGroup : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance hilbertGeneratorFiniteGroup : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance hilbertGeneratorFormsGroup : AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance hilbertGeneratorStableGroup : AddCommGroup (StableAutomorphicFunctions F n) :=
  Submodule.addCommGroup _
local instance hilbertGeneratorSpaceGroup (S : OperatorRealization F n) : AddCommGroup S.Space :=
  Submodule.addCommGroup _

namespace OperatorDeterminantSlice

variable [CompactSpace (AdeleQuotient F)] {r : ℕ} (T : CuspidalOperatorRealization F r)
  (hcoeff : CuspidalHilbertOrbitCoefficientStatement.{u})
  (χ : NumberField.IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ)
  (hχ : ∀ z, ‖(χ z : ℂ)‖ = 1) (hTχ : T.realization.HasCentralCharacter χ)
  (b : T.realization.UnitaryForm)
  (hb : ∀ f g : T.Space, b.inner f g =
    ∫ q, Inner.inner ℂ (toQuotient F (r + 1) T.realization f q)
      (toQuotient F (r + 1) T.realization g q)
      ∂(quotientHaarMeasure F (r + 1)).restrict (band F (r + 1)))

/-- The actual scalar integrals are the original Hilbert orbit coefficients. -/
theorem scalarCoefficientValues :
    Langlands.Archimedean.ScalarCoefficientValues
      (coordinateHilbertRepresentation T hcoeff χ hχ hTχ b hb)
      b.finiteForm.toHilbert
      (translatedHilbertEmbedding T.realization T.cuspidal (Nat.succ_ne_zero r) χ hχ hTχ b hb 1)
      (fun w v g => CuspidalHilbertOrbitCoefficient.coefficient T w v
        ((archimedeanGLCoordinates F (r + 1)).symm g)) :=
  Langlands.UnitaryEmbeddingFamily.scalarCoefficientValues_of_target
    (translatedHilbertEmbedding T.realization T.cuspidal (Nat.succ_ne_zero r) χ hχ hTχ b hb)
    (adelicHilbertRepresentation T hcoeff χ hχ hTχ b hb)
    (adelicHilbertRepresentation_realizes T hcoeff χ hχ hTχ b hb)
    (infiniteCoordinateInclusion F (r + 1)) b.finiteForm.toHilbert
    (fun a v => translatedToL2 T.realization T.cuspidal a v)
    (fun w v g => CuspidalHilbertOrbitCoefficient.coefficient T w v
      ((archimedeanGLCoordinates F (r + 1)).symm g))
    (translatedHilbertEmbedding_toHilbert T.realization T.cuspidal (Nat.succ_ne_zero r)
      χ hχ hTχ b hb)
    (fun w v g => inner_translatedToL2_left T w (infiniteCoordinateInclusion F (r + 1) g) v)


end OperatorDeterminantSlice
end Langlands.Automorphic
