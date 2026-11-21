import Langlands.Automorphic.CuspidalJointAdmissibility
import Langlands.Automorphic.CuspidalMixedHilbertEmbedding

/-! # Fixed-level density of the actual band source map -/

noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 65000

open scoped Classical CategoryTheory.MonObj Manifold ContDiff Matrix.Norms.Operator

namespace Langlands.Global.RankinSelbergGlobal.ArchimedeanWhittakerRegularity

open Langlands.Automorphic Langlands.Automorphic.CuspidalFixedSmoothDensity
  Langlands.Automorphic.OperatorDeterminantSlice Langlands.Global.ArchimedeanGL
  NumberField MeasureTheory Langlands.Archimedean Langlands.Archimedean.MixedSmooth

universe u

attribute [local instance] regSchemeAffine regSchemeSmooth regRationalAddCommGroup
  regContinuousAddCommGroup regSmoothAddCommGroup regFormsAddCommGroup regStableAddCommGroup
  regRealizationAddCommGroup finiteAdelicGL_nonarchimedeanGroup

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] {r : ℕ}
  (T : CuspidalOperatorRealization F r)

variable (χ : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ)
  (hχ : ∀ z, ‖(χ z : ℂ)‖ = 1) (hTχ : T.realization.HasCentralCharacter χ)
  (b : T.realization.UnitaryForm)
  (hb : ComputesBandInnerProduct T.realization b)

local notation "B" => adelicCompletion T χ hχ hTχ b hb
local notation "U" => OperatorUnitaryFormCore.AdelicCompletion.action B
local notation "σ" => finiteHilbertAction F (r + 1) U
local notation "π" => infiniteHilbertAction F (r + 1) U
local notation "j" => toBandHilbertSmooth T χ hχ hTχ b hb
local notation "hs" => bandHasSmoothCoordinateSource T χ hχ hTχ b hb

/-- The actual smooth source image is derivative-dense at every fixed level. -/
theorem bandDenseFixedImages :
    DenseFixedImages (A := ArchimedeanMatrix F (r + 1)) (G := ArchimedeanGL F (r + 1))
      T.realization.finiteRepresentation σ π j :=
  (B).coordinateDenseFixedImages hs
    (OperatorRealization.UnitaryForm.jointVectorRecovery b T.isJointlyAdmissible)

end Langlands.Global.RankinSelbergGlobal.ArchimedeanWhittakerRegularity
