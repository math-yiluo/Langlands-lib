import Langlands.Representation.RankinSelberg.GammaFromWhittakerType
import Langlands.LocalFactor.Abelian.Padic

/-! Canonical symmetric gamma construction inputs from the original Whittaker types.
This module defines a proposition; it does not prove the analytic or functional
equation results needed to establish it. -/

namespace Langlands.RankinSelberg

open HarmonicAnalysis Whittaker

universe uF uV uW

/-- The existing canonical symmetric construction input follows from standard
Whittaker type of both original representations, at any supplied self-dual measure.
This is a closed statement of the derived JPSS consequence, not its proof. -/
def WhittakerTypeGammaConstructionInputStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    (r n : ℕ) (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (W : Type uW) [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W),
    letI := F.canonicalTopologicalData.topology
    IsOfWhittakerType r (standardCharacter ψ r) π →
    IsOfWhittakerType n (standardCharacter ψ n) σ →
    PadicSymmetricGammaConstructionInput F ψ ν.val π σ

end Langlands.RankinSelberg
