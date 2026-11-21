import Langlands.Automorphic.CuspidalBandSourceDerivatives
import Langlands.Automorphic.CuspidalJointAdmissibility
import Langlands.Automorphic.OperatorBandHilbertNorm
import Langlands.Global.RankinSelberg.CuspidalMixedWhittakerModelOfCompletion

/-! # Whittaker source data on the actual determinant band -/

noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000
open scoped Classical CategoryTheory.MonObj Manifold ContDiff Matrix.Norms.Operator

namespace Langlands.Global.RankinSelbergGlobal.ArchimedeanWhittakerRegularity

open Langlands.Automorphic Langlands.Automorphic.CuspidalFixedSmoothDensity
  Langlands.Automorphic.OperatorDeterminantSlice Langlands.Global.ArchimedeanGL
  NumberField MeasureTheory

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
local notation "U" => OperatorUnitaryFormCore.AdelicCompletion.action B
local notation "σ" => finiteHilbertAction F (r + 1) U
local notation "π" => infiniteHilbertAction F (r + 1) U
local notation "c" => hilbertCoordinateActions_commute F (r + 1) U
local notation "hs" => bandHasSmoothCoordinateSource T χ hχ hTχ b hb

/-- The Whittaker source identities for the canonical determinant-band embedding. -/
def BandSmoothSourceWhittakerData : Prop :=
  ∀ (hL2 : ∀ w : T.Space, MemLp (toQuotient F (r + 1) T.realization w) 2
      ((quotientHaarMeasure F (r + 1)).restrict (band F (r + 1)))),
    SmoothSourceWhittakerData (E := b.finiteForm.HilbertCompletion) σ π c
      T.realization.finiteRepresentation T.realization.compactRepresentation
      (fun X => T.realization.envelopingAction
        (envelopingGenerator F (r + 1) (complexify F (r + 1) X)))
      (realLieAlgebraToMatrix F (r + 1))
      (fun w => ‖toL2 F (r + 1) T.realization (quotientHaarMeasure F (r + 1)) hL2 w‖)
      (toBandHilbertSmooth T χ hχ hTχ b hb) (toHilbertMixed T χ hχ hTχ b hb).toLinearMap

/-- The canonical band source has the actual Whittaker extension data. -/
theorem bandSmoothSourceWhittakerData : BandSmoothSourceWhittakerData T χ hχ hTχ b hb := by
  intro hL2
  exact (B).coordinateWhittakerData hs T.realization.finiteRepresentation_isSmooth
    (realLieAlgebraToMatrix F (r + 1))
    (fun w => ‖toL2 F (r + 1) T.realization (quotientHaarMeasure F (r + 1)) hL2 w‖)
    (fun w => norm_toL2_eq_toHilbert T.realization b hb hL2 w)
    (fun g x y => bandInfiniteAction_inner T χ hχ hTχ b hb g x y)
    (b.jointVectorRecovery T.isJointlyAdmissible)
    (bandRealGeneratorCompatibility T χ hχ hTχ b hb)

end Langlands.Global.RankinSelbergGlobal.ArchimedeanWhittakerRegularity
