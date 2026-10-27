import Langlands.Representation.Whittaker.TwoBlockOpenCell
import Langlands.Representation.Shahidi.LocalCoefficientPadic

/-!
# Whittaker scalar covariance of the actual two-block induction

The tensor product of two standard Whittaker functionals reads left multiplication
by an actual block diagonal unipotent as the product of the two characters.
-/

noncomputable section

namespace Langlands.Whittaker

open GeneralLinear HarmonicAnalysis

universe uF uV

/-- The scalar left-covariance needed for the two-block Jacquet integral, derived
from the actual normalized induction and the two factor Whittaker functionals. -/
def TwoBlockInducingWhittakerCovarianceStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (a b : ℕ)
    {V₁ V₂ : Type uV} [AddCommGroup V₁] [Module ℂ V₁]
    [AddCommGroup V₂] [Module ℂ V₂]
    (π₁ : Representation ℂ (Langlands.GeneralLinear (a + 1) F.Carrier) V₁)
    (π₂ : Representation ℂ (Langlands.GeneralLinear (b + 1) F.Carrier) V₂),
    letI := F.canonicalTopologicalData.topology
    ∀ ℓ₁ ∈ glFunctionals ψ a π₁, ∀ ℓ₂ ∈ glFunctionals ψ b π₂,
      ∀ (f : TwoBlockInducedCarrier F a b π₁ π₂)
        (u₁ : upperUnipotent (a + 1) F.Carrier)
        (u₂ : upperUnipotent (b + 1) F.Carrier)
        (g : Langlands.GeneralLinear (a + 1 + (b + 1)) F.Carrier),
        Shahidi.pairFunctional ℓ₁ ℓ₂
            (twoBlockEval F a b π₁ π₂ f (blockSum (u₁.val, u₂.val) * g)) =
          ((standardCharacter ψ a u₁ : ℂ) * (standardCharacter ψ b u₂ : ℂ)) *
            Shahidi.pairFunctional ℓ₁ ℓ₂ (twoBlockEval F a b π₁ π₂ f g)

end Langlands.Whittaker
