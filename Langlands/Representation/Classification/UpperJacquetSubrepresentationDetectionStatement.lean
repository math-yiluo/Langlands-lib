import Langlands.Representation.Classification.CuspidalJacquetMultiplicityStatement

/-! Positive upper-Jacquet counts for actual subrepresentations of induction. -/

namespace Langlands

open CuspidalJacquetMultiplicity

universe uF uV uW

/-- An actual nonzero subrepresentation of normalized upper induction has
a positive bounded inducing-type count in its upper Jacquet module whenever
the ambient upper Jacquet module has a supplied actual-series count. -/
def UpperJacquetSubrepresentationDetectionStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ) (B : GeneralLinear.BlockShape n)
      (σ : Rep.{uV} ℂ (B.Levi F.Carrier)),
      Representation.IsIrreducible σ.ρ →
      ∀ (P : Rep.{uW} ℂ (GeneralLinear n F.Carrier))
        (j : P.ρ.IntertwiningMap (induced T B σ).ρ),
        Function.Injective j → j ≠ 0 →
        ∀ M : ℕ,
          HasJordanHolderMultiplicity (upperJacquet T B (induced T B σ)) σ M →
          ∃ m : ℕ, HasJordanHolderMultiplicity (upperJacquet T B P) σ m ∧
            0 < m ∧ m ≤ M

end Langlands
