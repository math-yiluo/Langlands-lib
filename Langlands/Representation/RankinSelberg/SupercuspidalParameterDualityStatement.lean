import Langlands.Representation.RankinSelberg.SupercuspidalTwistParameters

namespace Langlands.RankinSelberg

universe uF uV uW

/-- Smooth duality inverts the contragredient unramified-twist parameter.
Admissibility supplies the reverse implication through smooth biduality. -/
def SupercuspidalParameterDualityStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p),
    letI := F.canonicalTopologicalData.topology
    ∀ (r : ℕ),
    letI := F.canonicalTopologicalData.generalLinearTopologicalGroup (r + 1)
    ∀ {V : Type uV} [AddCommGroup V] [Module ℂ V]
      {W : Type uW} [AddCommGroup W] [Module ℂ W]
      (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
      (σ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) W),
      IsAdmissible π → IsAdmissible σ →
      ∀ a : ℂ,
        IsContragredientTwistParameter F
            (smoothContragredient π) (smoothContragredient σ) a⁻¹ ↔
          IsContragredientTwistParameter F π σ a

end Langlands.RankinSelberg
