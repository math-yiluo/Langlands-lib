import Langlands.Representation.Classification.RelativeJacquetMultiplicityStatement

/-! Positivity of a supplied actual inner Jacquet count detects an inner quotient. -/

noncomputable section

namespace Langlands

open GeneralLinear Geometric RelativeJacquetMultiplicity

universe uF uV uW

/-- A supplied actual fine-cuspidal multiplicity in the inner opposite Jacquet
module is positive exactly when the corresponding inner induction has the
specified irreducible admissible quotient. -/
def GLRelativeInnerJacquetPositiveQuotientStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ), 0 < n → ∀ (B : BlockShape n) (S : BlockRefinement B)
      (ω : Rep.{uV} ℂ ((B.flatten S).Levi F.Carrier)),
      Representation.IsIrreducible ω.ρ →
      CuspidalSupport.IsLeviCuspidal (B.flatten S) ω.ρ →
      ∀ (v₀ : Fin (B.flatten S).length → ℝ) (t : Fin B.length → ℝ),
        let τ := fineTwist T B S ω v₀ t
        ∀ (μ : Rep.{uW} ℂ (B.Levi F.Carrier)),
          Representation.IsIrreducible μ.ρ → IsAdmissible μ.ρ →
          ∀ (m : ℕ), HasJordanHolderMultiplicity (innerJacquet T B S μ) τ m →
            (0 < m ↔ ∃ q : (innerInduced T B S τ).ρ.IntertwiningMap μ.ρ,
              Function.Surjective q)

end Langlands
