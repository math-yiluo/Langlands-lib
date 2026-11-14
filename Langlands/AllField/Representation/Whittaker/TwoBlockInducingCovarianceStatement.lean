import Langlands.Representation.Whittaker.TwoBlockInducingCovarianceStatement
import Langlands.AllField.Group.GL.CompactOpenSupplement
import Langlands.AllField.Representation.Shahidi.IntertwiningCovariance
import Langlands.AllField.Representation.Whittaker.TwoBlockOpenCell
/-!
# Whittaker scalar covariance of the actual two-block induction

The tensor product of two standard Whittaker functionals reads left multiplication
by an actual block diagonal unipotent as the product of the two characters.
-/

noncomputable section

namespace Langlands.AllField.Whittaker
open Langlands.Whittaker hiding TwoBlockInducedCarrier TwoBlockInducingWhittakerCovarianceStatement hasCompactSupport_twoBlockCellRestriction twoBlockCell twoBlockCellInclusion twoBlockCellInclusion_apply twoBlockCellPoint twoBlockCellRestriction twoBlockCellSubmodule twoBlockEval twoBlockInduced twoBlockInducingRepresentation twoBlockParabolic twoBlockRestriction
open Langlands.AllField.Whittaker

open Langlands.GeneralLinear
open Langlands.HarmonicAnalysis hiding padicRectangularHaarScaling padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis

universe uF uV

/-- The scalar left-covariance needed for the two-block Jacquet integral, derived
from the actual normalized induction and the two factor Whittaker functionals. -/
def TwoBlockInducingWhittakerCovarianceStatement : Prop :=
  ∀ (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (ψ : UnitaryAdditiveCharacter F)
    (a b : ℕ)
    {V₁ V₂ : Type uV} [AddCommGroup V₁] [Module ℂ V₁]
    [AddCommGroup V₂] [Module ℂ V₂]
    (π₁ : Representation ℂ (Langlands.GeneralLinear (a + 1) F) V₁)
    (π₂ : Representation ℂ (Langlands.GeneralLinear (b + 1) F) V₂),
    ∀ ℓ₁ ∈ glFunctionals ψ a π₁, ∀ ℓ₂ ∈ glFunctionals ψ b π₂,
      ∀ (f : TwoBlockInducedCarrier F a b π₁ π₂)
        (u₁ : upperUnipotent (a + 1) F)
        (u₂ : upperUnipotent (b + 1) F)
        (g : Langlands.GeneralLinear (a + 1 + (b + 1)) F),
        Shahidi.pairFunctional ℓ₁ ℓ₂
            (twoBlockEval F a b π₁ π₂ f (blockSum (u₁.val, u₂.val) * g)) =
          ((standardCharacter ψ a u₁ : ℂ) * (standardCharacter ψ b u₂ : ℂ)) *
            Shahidi.pairFunctional ℓ₁ ℓ₂ (twoBlockEval F a b π₁ π₂ f g)

end Langlands.AllField.Whittaker
