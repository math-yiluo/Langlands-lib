import Langlands.AlgebraicGeometry.Picard.AmpleSectionOpenBasisProof
import Langlands.AlgebraicGeometry.Picard.FiniteSectionAvoidanceProof

/-! # A finite set inside a whole section generation open of an ample line bundle -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

/-- Every finite set inside an open lies in a whole generation open of a
positive-power section of an ample line bundle, contained in the given open. -/
theorem ampleFiniteSetSection : AmpleFiniteSetSectionStatement.{u} := by
  intro X L hL E W hE hEW
  exact finiteSectionAvoidance X L (ampleSectionOpenBasis X L hL) E W hE hEW

/-- A direct consumer of the finite-set ample section-open theorem. -/
theorem ampleFiniteSetSection_apply (X : Scheme.{u}) (L : LineBundle X)
    (hL : L.IsAmple) (E : Set X) (W : X.Opens) (hE : E.Finite)
    (hEW : E ⊆ (W : Set X)) :
    ∃ n : ℕ, 1 ≤ n ∧ ∃ s : L.powSections n,
      E ⊆ (L.sectionOpen s : Set X) ∧ L.sectionOpen s ≤ W :=
  ampleFiniteSetSection X L hL E W hE hEW

end Langlands.AlgebraicGeometry.Picard
