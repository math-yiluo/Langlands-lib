import Langlands.Representation.Whittaker.TwoBlockOpenCell
import Langlands.Representation.RankinSelberg.LocalFactor
import Langlands.Representation.Shahidi.LocalCoefficientPadic
import Langlands.HarmonicAnalysis.PadicScalarHaarScalingProof

/-! # Scalar coefficients of pure-tensor two-block cell sections -/

noncomputable section

namespace Langlands.Whittaker

open HarmonicAnalysis MeasureTheory

universe uF uV

/-- A pure-tensor cell section gives an actual Whittaker coefficient with the
scalar twisted rectangular integral and the original positive half modulus. -/
def TwoBlockCellCoefficientStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (a b : ℕ)
    {V₁ V₂ : Type uV} [AddCommGroup V₁] [Module ℂ V₁]
    [AddCommGroup V₂] [Module ℂ V₂]
    (π₁ : Representation ℂ (Langlands.GeneralLinear (a + 1) F.Carrier) V₁)
    (π₂ : Representation ℂ (Langlands.GeneralLinear (b + 1) F.Carrier) V₂),
    (letI := F.canonicalTopologicalData.topology; IsSmooth π₁) →
    (letI := F.canonicalTopologicalData.topology; IsSmooth π₂) →
    let T := F.canonicalTopologicalData
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := T.secondCountableTopology
    letI := T.fieldT2
    letI := borel F.Carrier
    letI : BorelSpace F.Carrier := ⟨rfl⟩
    ∀ (ψ : UnitaryAdditiveCharacter F.Carrier)
      (ℓ₁ : V₁ →ₗ[ℂ] ℂ), ℓ₁ ∈ glFunctionals ψ a π₁ →
      ∀ (ℓ₂ : V₂ →ₗ[ℂ] ℂ), ℓ₂ ∈ glFunctionals ψ b π₂ →
      ∀ (μ : Measure (Matrix (Fin (b + 1)) (Fin (a + 1)) F.Carrier))
        [μ.IsAddHaarMeasure]
        (Ψ : SchwartzBruhat (Matrix (Fin (b + 1)) (Fin (a + 1)) F.Carrier))
        (v₁ : V₁) (v₂ : V₂),
        ∃ W ∈ RankinSelberg.whittakerSet ψ (a + 1 + b)
            (twoBlockInduced F a b π₁ π₂),
          ∀ g : Langlands.GeneralLinear (b + 1) F.Carrier,
            let s := Shahidi.swapRank (a + 1) (b + 1) F.Carrier
              (GeneralLinear.blockSum (g, 1))
            let m := (Shahidi.twoBlockLeviEquiv
              (Nat.succ_pos a) (Nat.succ_pos b) F.Carrier).symm (1, g)
            W.val s = ((T.leviHalfModulus (twoBlockShape a b) m : ℂˣ) : ℂ) *
              (ℓ₁ v₁ * ℓ₂ (π₂ g v₂)) *
              ∫ x, ψ.complex (-(x (Fin.last b) 0)) * Ψ (g⁻¹.val * x) ∂μ

end Langlands.Whittaker
