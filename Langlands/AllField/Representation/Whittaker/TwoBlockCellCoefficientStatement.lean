import Langlands.Representation.Whittaker.TwoBlockCellCoefficientStatement
import Langlands.AllField.Group.GL.CompactOpenSupplement
import Langlands.AllField.Representation.Shahidi.IntertwiningCovariance
import Langlands.AllField.Representation.Whittaker.TwoBlockOpenCell
/-! # Scalar coefficients of pure-tensor two-block cell sections -/

noncomputable section

namespace Langlands.AllField.Whittaker
open Langlands.Whittaker hiding TwoBlockCellCoefficientStatement TwoBlockInducedCarrier hasCompactSupport_twoBlockCellRestriction twoBlockCell twoBlockCellInclusion twoBlockCellInclusion_apply twoBlockCellPoint twoBlockCellRestriction twoBlockCellSubmodule twoBlockEval twoBlockInduced twoBlockInducingRepresentation twoBlockParabolic twoBlockRestriction
open Langlands.AllField.Whittaker

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis hiding padicRectangularHaarScaling padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis

universe uF uV

/-- A pure-tensor cell section gives an actual Whittaker coefficient with the
scalar twisted rectangular integral and the original positive half modulus. -/
def TwoBlockCellCoefficientStatement : Prop :=
  ∀ (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (a b : ℕ)
    {V₁ V₂ : Type uV} [AddCommGroup V₁] [Module ℂ V₁]
    [AddCommGroup V₂] [Module ℂ V₂]
    (π₁ : Representation ℂ (Langlands.GeneralLinear (a + 1) F) V₁)
    (π₂ : Representation ℂ (Langlands.GeneralLinear (b + 1) F) V₂),
    (IsSmooth π₁) →
    (IsSmooth π₂) →
    let T := (⟨⟩ : LocalFieldData F)
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := T.secondCountableTopology
    letI := T.fieldT2
    letI := borel F
    letI : BorelSpace F := ⟨rfl⟩
    ∀ (ψ : UnitaryAdditiveCharacter F)
      (ℓ₁ : V₁ →ₗ[ℂ] ℂ), ℓ₁ ∈ glFunctionals ψ a π₁ →
      ∀ (ℓ₂ : V₂ →ₗ[ℂ] ℂ), ℓ₂ ∈ glFunctionals ψ b π₂ →
      ∀ (μ : Measure (Matrix (Fin (b + 1)) (Fin (a + 1)) F))
        [μ.IsAddHaarMeasure]
        (Ψ : SchwartzBruhat (Matrix (Fin (b + 1)) (Fin (a + 1)) F))
        (v₁ : V₁) (v₂ : V₂),
        ∃ W ∈ RankinSelberg.whittakerSet ψ (a + 1 + b)
            (twoBlockInduced F a b π₁ π₂),
          ∀ g : Langlands.GeneralLinear (b + 1) F,
            let s := Shahidi.swapRank (a + 1) (b + 1) F
              (GeneralLinear.blockSum (g, 1))
            let m := (Shahidi.twoBlockLeviEquiv
              (Nat.succ_pos a) (Nat.succ_pos b) F).symm (1, g)
            W.val s = ((T.leviHalfModulus (twoBlockShape a b) m : ℂˣ) : ℂ) *
              (ℓ₁ v₁ * ℓ₂ (π₂ g v₂)) *
              ∫ x, ψ.complex (-(x (Fin.last b) 0)) * Ψ (g⁻¹.val * x) ∂μ

end Langlands.AllField.Whittaker
