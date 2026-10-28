import Langlands.Representation.Classification.RelativeJacquetMultiplicityStatement
import Langlands.Representation.Filtration.ObjectDefinitions

/-! Actual finite-series summation across a supplied coarse-Levi filtration
for the inner and ambient relative opposite Jacquet constructions. -/

open scoped BigOperators

namespace Langlands

open GeneralLinear Geometric

universe uF uV uW

namespace RelativeJacquetMultiplicity

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
  (T : F.TopologicalData) {n : ℕ} (B : BlockShape n) (S : BlockRefinement B)

/-- Actual inner opposite Jacquet multiplicities decompose over every original
grade of the supplied smooth coarse-Levi filtration. -/
def InnerFiltrationMultiplicityClause : Prop :=
  letI := T.topology
  ∀ (A : Rep.{uV} ℂ (B.Levi F.Carrier)),
    IsSmooth A.ρ →
      ∀ (l : ℕ) (s : ObjectRepFiltration A l)
        (τ : Rep.{uW} ℂ (refinedLevi F.Carrier B S)) (m : ℕ),
        HasJordanHolderMultiplicity (innerJacquet T B S A) τ m ↔
          ∃ counts : Fin l → ℕ,
            (∀ i : Fin l, HasJordanHolderMultiplicity
              (innerJacquet T B S (s.gradedRepresentation i)) τ (counts i)) ∧
            (∑ i : Fin l, counts i) = m

/-- The same finite-series criterion after actual outer normalized induction
and composed opposite Jacquet, using the original coarse-Levi grades. -/
def AmbientFiltrationMultiplicityClause : Prop :=
  letI := T.topology
  ∀ (A : Rep.{uV} ℂ (B.Levi F.Carrier)),
    IsSmooth A.ρ →
      ∀ (l : ℕ) (s : ObjectRepFiltration A l)
        (τ : Rep.{uW} ℂ (refinedLevi F.Carrier B S)) (m : ℕ),
        HasJordanHolderMultiplicity (ambientJacquet T B S A) τ m ↔
          ∃ counts : Fin l → ℕ,
            (∀ i : Fin l, HasJordanHolderMultiplicity
              (ambientJacquet T B S (s.gradedRepresentation i)) τ (counts i)) ∧
            (∑ i : Fin l, counts i) = m

end RelativeJacquetMultiplicity

/-- Both relative finite-filtration multiplicity criteria, with independent
field, coarse-Levi input and refined-Levi constituent universes. -/
def GLRelativeJacquetFiltrationMultiplicityStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
    (n : ℕ) (B : BlockShape n) (S : BlockRefinement B),
    RelativeJacquetMultiplicity.InnerFiltrationMultiplicityClause.{uF, uV, uW}
        F T B S ∧
    RelativeJacquetMultiplicity.AmbientFiltrationMultiplicityClause.{uF, uV, uW}
        F T B S

end Langlands
