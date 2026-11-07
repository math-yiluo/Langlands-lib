import Langlands.Representation.Category.Subquotients
import Langlands.Representation.Unitary.UnitarizabilityContinuationProof

/-! A compact-fixed reduction of openness for actual smooth families. -/

namespace Langlands.Plancherel

open MeasureTheory

/-- A common compact open subgroup detecting every irreducible subquotient
transfers matrix openness to actual smooth representations. -/
def CompactFixedFamilyOpennessStatement.{uX, uG, uV, un} : Prop :=
  ∀ (X : Type uX) [TopologicalSpace X]
    (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure]
    (A : X → SmoothRep.{0, uG, uV} ℂ G)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (n : Type un) [Fintype n]
    (e : ∀ x, Module.Basis n ℂ (fixedVectors (A x).representation K.toSubgroup)),
    (∀ x, Nontrivial (A x)) →
    (∀ x (D : SmoothRep.{0, uG, uV} ℂ G),
      D.IsIrreducible → SmoothRep.IsSubquotient D (A x) →
        ∃ v : D, v ∈ fixedVectors D.representation K.toSubgroup ∧ v ≠ 0) →
    (∀ g i j, Continuous (fun x =>
      UnitarizabilityContinuation.fixedMatrix μ (A x).isSmooth hK (e x)
        (A x).representation g i j)) →
    IsOpen {x | (A x).IsIrreducible}

end Langlands.Plancherel
