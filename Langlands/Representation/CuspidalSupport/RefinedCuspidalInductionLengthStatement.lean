import Langlands.Representation.CuspidalSupport.LeviDefinitions
import Langlands.Representation.Geometric.FlattenedLevi
import Langlands.Representation.Geometric.RefinementFunctors
import Langlands.Representation.Filtration.ObjectDefinitions
import Mathlib.RingTheory.FiniteLength

/-! Admissibility and finite length targets for actual refined cuspidal induction. -/

noncomputable section

namespace Langlands.CuspidalSupport

open GeneralLinear Geometric

universe uF uV

/-- Actual normalized refined induction of irreducible cuspidal data is
admissible and has finite group-algebra length and an actual composition series. -/
def RefinedCuspidalInductionFiniteLengthStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ) (B : BlockShape n) (S : BlockRefinement B)
      (ω : Rep.{uV} ℂ ((B.flatten S).Levi F.Carrier)),
      Representation.IsIrreducible ω.ρ →
      IsLeviCuspidal (B.flatten S) ω.ρ →
        letI := T.leviTopologicalGroup B
        let σ := ω.ρ.comp (flattenedLeviEquiv F.Carrier B S).symm.toMonoidHom
        let I : Rep.{max uF uV} ℂ (B.Levi F.Carrier) :=
          Rep.of (T.normalizedRefinedInduced B S σ)
        IsAdmissible I.ρ ∧
          IsFiniteLength (MonoidAlgebra ℂ (B.Levi F.Carrier)) I.ρ.asModule ∧
          ∃ m : ℕ, HasCompositionSeriesLength I m

end Langlands.CuspidalSupport
