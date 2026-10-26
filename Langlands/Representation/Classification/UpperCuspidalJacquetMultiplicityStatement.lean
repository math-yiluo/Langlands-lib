import Langlands.Representation.Classification.CuspidalJacquetMultiplicityStatement
import Langlands.Representation.CuspidalSupport.JacquetInductionStatement

/-! Exact upper cuspidal Jacquet counts, conditional on the actual filtration. -/

namespace Langlands

open CuspidalSupport

universe uF uV uW

/-- The algebraic upper-clause adapter: the actual associated Jacquet
filtration gives exact length and all single-factor multiplicities. -/
def GLUpperCuspidalJacquetMultiplicityFromFiltrationStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) (n : ℕ),
    AssociatedJacquetFiltrationTheorem.{uF, uV} F T n →
    letI := T.topology
    ∀ (B C : GeneralLinear.BlockShape n)
      (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (ρ : Representation ℂ (B.Levi F.Carrier) V),
      Representation.IsIrreducible ρ → IsLeviCuspidal B ρ →
      LevisAssociated (F := F.Carrier) B C →
        let Ju := CuspidalJacquetMultiplicity.upperJacquet T C
          (CuspidalJacquetMultiplicity.induced T B (Rep.of ρ))
        HasCompositionSeriesLength Ju
          (Nat.card (MinimalConjugatingPermutations (F := F.Carrier) B C)) ∧
        ∀ (W : Type uW) [AddCommGroup W] [Module ℂ W]
          (τ : Representation ℂ (C.Levi F.Carrier) W) (m : ℕ),
          HasJordanHolderMultiplicity Ju (Rep.of τ) m ↔
            m = Nat.card (AssociatingPermutations B C ρ τ)

end Langlands
