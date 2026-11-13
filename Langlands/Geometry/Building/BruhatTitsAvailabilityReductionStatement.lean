import Langlands.Geometry.Building.GroupAxiomsExistenceStatement
import Langlands.Geometry.Building.BruhatTitsAvailabilityStatement

/-! # Bruhat–Tits availability from the one-group clauses of corrected Definition 4.1.26 -/

universe u

namespace Langlands.Geometry.Building

/-- If every connected reductive group over every nonarchimedean local field in universe `u`
carries data satisfying the clauses of corrected KP Definition 4.1.26 that concern the group
alone (`GroupAxiomsExistenceStatement`), then some assignment of such data satisfies all ten
corrected axioms, including the comparisons between groups of Axiom 4.1.1 and Axiom 4.1.17
(`BruhatTitsAvailabilityStatement`, the Definition 4.1.26 conclusion of KP Theorem 9.2.7).
This is a statement of the implication only; neither side is asserted. -/
def BruhatTitsAvailabilityReductionStatement : Prop :=
  GroupAxiomsExistenceStatement.{u} → BruhatTitsAvailabilityStatement.{u}

end Langlands.Geometry.Building
