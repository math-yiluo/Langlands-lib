import Langlands.Representation.Classification.CuspidalJacquetMultiplicityStatement

/-! Positive opposite-Jacquet counts for admissible quotients of induction. -/

namespace Langlands

open CuspidalJacquetMultiplicity

universe uF uV uW

/-- An admissible nonzero quotient of normalized upper induction has a positive
bounded inducing-type count in its opposite normalized Jacquet module whenever
the ambient opposite Jacquet module has a supplied actual-series count. -/
def OppositeJacquetQuotientDetectionStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ), 0 < n → ∀ (B : GeneralLinear.BlockShape n)
      (σ : Rep.{uV} ℂ (B.Levi F.Carrier)),
      Representation.IsIrreducible σ.ρ → IsAdmissible σ.ρ →
      ∀ (P : Rep.{uW} ℂ (GeneralLinear n F.Carrier)),
        IsAdmissible P.ρ →
        ∀ (q : (induced T B σ).ρ.IntertwiningMap P.ρ),
          Function.Surjective q → q ≠ 0 →
          ∀ M : ℕ,
            HasJordanHolderMultiplicity (oppositeJacquet T B (induced T B σ)) σ M →
            ∃ m : ℕ, HasJordanHolderMultiplicity (oppositeJacquet T B P) σ m ∧
              0 < m ∧ m ≤ M

end Langlands
