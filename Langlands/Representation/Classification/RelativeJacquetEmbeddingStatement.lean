import Langlands.Representation.Classification.RelativeJacquetMultiplicityStatement

/-! Actual relative opposite-Jacquet embeddings and bounded finite-series counts. -/

noncomputable section

namespace Langlands

open GeneralLinear Geometric RelativeJacquetMultiplicity

universe uF uV uW

/-- An irreducible admissible coarse-Levi representation gives an actual
inner-to-ambient opposite-Jacquet injection. Every supplied actual ambient
Jordan--Hölder count then supplies an actual inner count bounded by it. -/
def GLRelativeJacquetEmbeddingStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ), 0 < n → ∀ (B : BlockShape n) (S : BlockRefinement B)
      (μ : Rep.{uW} ℂ (B.Levi F.Carrier)),
      Representation.IsIrreducible μ.ρ → IsAdmissible μ.ρ →
      (∃ j : (innerJacquet T B S μ).ρ.IntertwiningMap
          (ambientJacquet T B S μ).ρ, Function.Injective j) ∧
      ∀ (τ : Rep.{uV} ℂ (refinedLevi F.Carrier B S)) (M : ℕ),
        HasJordanHolderMultiplicity (ambientJacquet T B S μ) τ M →
        ∃ m : ℕ, HasJordanHolderMultiplicity (innerJacquet T B S μ) τ m ∧ m ≤ M

end Langlands
