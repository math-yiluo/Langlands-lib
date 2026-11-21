import Langlands.Automorphic.AdelicCompletionSmoothSource
import Langlands.Automorphic.CuspidalHilbertAdelicCompletion
import Langlands.Global.RankinSelberg.ArchimedeanWhittakerRegularity
import Langlands.Representation.Archimedean.HilbertSmoothKernelProof

/-! # The original carrier in the actual mixed smooth space -/

noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 15000

open scoped Classical CategoryTheory.MonObj Manifold ContDiff Matrix.Norms.Operator

namespace Langlands.Automorphic.OperatorDeterminantSlice

open Langlands.Global Langlands.Global.ArchimedeanGL Langlands.Automorphic.CuspidalFixedSmoothDensity
  Langlands.Archimedean Langlands.Archimedean.MixedSmooth NumberField MeasureTheory
  Langlands.Global.RankinSelbergGlobal.ArchimedeanWhittakerRegularity

universe u

attribute [local instance] regRationalAddCommGroup regContinuousAddCommGroup regSmoothAddCommGroup
  regFormsAddCommGroup regStableAddCommGroup regRealizationAddCommGroup

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] {r : ℕ}
  (T : CuspidalOperatorRealization F r)
  (χ : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ)
  (hχ : ∀ z, ‖(χ z : ℂ)‖ = 1) (hTχ : T.realization.HasCentralCharacter χ)
  (b : T.realization.UnitaryForm)
  (hb : ComputesBandInnerProduct T.realization b)

local notation "hcoeff" => cuspidalHilbertOrbitCoefficient
local notation "hkernel" => Langlands.Archimedean.hilbertSmoothKernel
local notation "B" => adelicCompletion T χ hχ hTχ b hb

/-- The original vectors are genuinely smooth in the actual coordinate restriction. -/
theorem bandHasSmoothCoordinateSource : (B).HasSmoothCoordinateSource :=
  toHilbert_isSmoothVector T hcoeff χ hχ hTχ b hb hkernel

/-- The original map to the smooth vectors of the infinite coordinate action. -/
def toBandHilbertSmooth :=
  (B).coordinateSmoothSource (bandHasSmoothCoordinateSource T χ hχ hTχ b hb)

/-- The canonical original map into the genuine mixed smooth vectors of
the actual reconstructed Hilbert action. -/
def toHilbertMixed :=
  (B).coordinateMixedSource (bandHasSmoothCoordinateSource T χ hχ hTχ b hb)
    T.realization.finiteRepresentation_isSmooth

end Langlands.Automorphic.OperatorDeterminantSlice
