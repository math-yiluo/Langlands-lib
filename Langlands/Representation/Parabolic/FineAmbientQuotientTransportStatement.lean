import Langlands.Representation.Classification.RelativeRecoveryStatement

/-! Fine-to-ambient transport of specified surjective quotient maps. -/

noncomputable section

namespace Langlands

open GeneralLinear Geometric RelativeJacquetMultiplicity

universe uF uV uW uZ

/-- A specified quotient `π` of the fine inner induction and a specified
quotient of the outer induction of a coarse real twist of `π` give an actual
quotient of the corresponding fine ambient induction. -/
def FineAmbientQuotientTransportStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ) (B : BlockShape n) (S : BlockRefinement B)
      (ω : Rep.{uV} ℂ ((B.flatten S).Levi F.Carrier)),
      IsSmooth ω.ρ →
      ∀ (v₀ : Fin (B.flatten S).length → ℝ) (t : Fin B.length → ℝ)
        (π : Rep.{uW} ℂ (B.Levi F.Carrier))
        (q₀ : (innerInduced T B S (fineTwist T B S ω v₀ 0)).ρ.IntertwiningMap π.ρ),
        Function.Surjective q₀ →
        ∀ (J : Rep.{uZ} ℂ (GeneralLinear n F.Carrier))
          (q : (CuspidalJacquetMultiplicity.induced T B
            (Rep.of (T.leviRealPowerTwist B t π.ρ))).ρ.IntertwiningMap J.ρ),
          Function.Surjective q →
          ∃ qf : (RelativeRecovery.fineAmbientInduced T B S ω v₀ t).ρ.IntertwiningMap J.ρ,
            Function.Surjective qf

end Langlands
