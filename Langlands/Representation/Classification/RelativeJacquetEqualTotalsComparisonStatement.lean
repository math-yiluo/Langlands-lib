import Langlands.Representation.Classification.RelativeJacquetMultiplicityStatement
import Langlands.Representation.Filtration.ObjectDefinitions

/-! The algebraic constituent comparison from equal actual Jacquet totals. -/

noncomputable section

namespace Langlands

open GeneralLinear Geometric RelativeJacquetMultiplicity

universe uF uV uW uX

/-- Equal actual relative Jacquet totals along a supplied admissible composition
series imply equal actual counts for every irreducible admissible subquotient. -/
def GLRelativeJacquetEqualTotalsComparisonStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ), 0 < n → ∀ (B : BlockShape n) (S : BlockRefinement B)
      (A : Rep.{uV} ℂ (B.Levi F.Carrier)),
      IsSmooth A.ρ →
      ∀ (l : ℕ) (s : ObjectRepFiltration A l),
        s.HasSimpleFactors →
        (∀ i : Fin l, IsAdmissible (s.gradedRepresentation i).ρ) →
        ∀ (τ : Rep.{uW} ℂ (refinedLevi F.Carrier B S)) (N : ℕ),
          HasJordanHolderMultiplicity (innerJacquet T B S A) τ N →
          HasJordanHolderMultiplicity (ambientJacquet T B S A) τ N →
          ∀ (μ : Rep.{uX} ℂ (B.Levi F.Carrier)),
            Representation.IsIrreducible μ.ρ → IsAdmissible μ.ρ →
            (∃ U : Subrepresentation A.ρ,
              ∃ q : U.toRepresentation.IntertwiningMap μ.ρ, Function.Surjective q) →
            ∃ m : ℕ,
              HasJordanHolderMultiplicity (innerJacquet T B S μ) τ m ∧
              HasJordanHolderMultiplicity (ambientJacquet T B S μ) τ m

end Langlands
