import Langlands.Representation.Classification.RelativeJacquetMultiplicityStatement

/-! A conditional strong-head adapter for actual GL induction and Jacquet counts. -/

noncomputable section

namespace Langlands

open GeneralLinear Geometric RelativeJacquetMultiplicity

universe uF uV uW

/-- Equal positive actual inner and ambient opposite-Jacquet counts force a
strong irreducible head of the actual finite-length outer induction. -/
def GLRelativePositiveTotalHeadStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ), 0 < n → ∀ (B : BlockShape n) (S : BlockRefinement B)
      (τ : Rep.{uV} ℂ (refinedLevi F.Carrier B S))
      (μ : Rep.{uW} ℂ (B.Levi F.Carrier)),
      Representation.IsIrreducible μ.ρ → IsAdmissible μ.ρ →
      IsFiniteLength (MonoidAlgebra ℂ (GeneralLinear n F.Carrier))
        (CuspidalJacquetMultiplicity.induced T B μ).ρ.asModule →
      ∀ (m : ℕ), 0 < m →
        HasJordanHolderMultiplicity (innerJacquet T B S μ) τ m →
        HasJordanHolderMultiplicity (ambientJacquet T B S μ) τ m →
        Classification.HasIrreducibleHead (CuspidalJacquetMultiplicity.induced T B μ).ρ

end Langlands
