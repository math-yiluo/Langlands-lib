import Langlands.Automorphic.CuspidalMixedHilbertEmbedding
import Langlands.Automorphic.CuspidalHilbertRealGenerators

/-! # Unitarity and real generators for the band coordinate action -/

noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000

open scoped Classical CategoryTheory.MonObj Manifold ContDiff Matrix.Norms.Operator

namespace Langlands.Automorphic.OperatorDeterminantSlice

open Langlands.Global Langlands.Global.ArchimedeanGL Langlands.Archimedean
  Langlands.Automorphic.CuspidalFixedSmoothDensity NumberField
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

local notation "B" => adelicCompletion T χ hχ hTχ b hb
local notation "π" =>
  infiniteHilbertAction F (r + 1) (OperatorUnitaryFormCore.AdelicCompletion.action B)

/-- The genuine coordinate restriction preserves the ambient inner product. -/
theorem bandInfiniteAction_inner (g : ArchimedeanGL F (r + 1))
    (x y : b.finiteForm.HilbertCompletion) :
    Inner.inner ℂ (π g x) (π g y) = Inner.inner ℂ x y :=
  (adelicHilbertRepresentation_realizes T cuspidalHilbertOrbitCoefficient χ hχ hTχ b hb).2
    (infiniteCoordinateInclusion F (r + 1) g) x y

/-- The band action computes genuine derivatives in the real Lie directions
of the original operator realization. -/
theorem bandRealGeneratorCompatibility :
    RealGeneratorCompatibility π b.finiteForm.toHilbert
      (fun X w => T.realization.envelopingAction
        (envelopingGenerator F (r + 1) (complexify F (r + 1) X)) w)
      (realLieAlgebraToMatrix F (r + 1)) :=
  realGeneratorCompatibility T cuspidalHilbertOrbitCoefficient χ hχ hTχ b hb hilbertSmoothKernel

end Langlands.Automorphic.OperatorDeterminantSlice
