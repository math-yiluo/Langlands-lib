import Langlands.Representation.Classification.RelativeJacquetMultiplicityStatement

/-! Positive inner counts from actual ambient counts and supported quotients. -/

noncomputable section

namespace Langlands

open GeneralLinear Geometric RelativeJacquetMultiplicity

universe uF uV uW

/-- At every real coarse parameter, a supported irreducible admissible quotient
has positive inner multiplicity bounded by each supplied actual ambient count. -/
def GLSupportedRelativeJacquetPositiveBoundStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ), 0 < n → ∀ (B : BlockShape n) (S : BlockRefinement B)
      (ω : Rep.{uV} ℂ ((B.flatten S).Levi F.Carrier)),
      Representation.IsIrreducible ω.ρ →
      CuspidalSupport.IsLeviCuspidal (B.flatten S) ω.ρ →
      ∀ (v₀ : Fin (B.flatten S).length → ℝ)
        (π : Rep.{uW} ℂ (B.Levi F.Carrier)),
        Representation.IsIrreducible π.ρ → IsAdmissible π.ρ →
        (∃ q₀ : (innerInduced T B S (fineTwist T B S ω v₀ 0)).ρ.IntertwiningMap π.ρ,
          Function.Surjective q₀) →
        ∀ t : Fin B.length → ℝ,
          let τ := fineTwist T B S ω v₀ t
          let πt := Rep.of (T.leviRealPowerTwist B t π.ρ)
          ∀ M : ℕ, HasJordanHolderMultiplicity (ambientJacquet T B S πt) τ M →
            ∃ m : ℕ, 0 < m ∧
              HasJordanHolderMultiplicity (innerJacquet T B S πt) τ m ∧ m ≤ M

end Langlands
