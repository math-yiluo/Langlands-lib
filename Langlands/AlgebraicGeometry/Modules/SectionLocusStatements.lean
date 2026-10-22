import Langlands.AlgebraicGeometry.Modules.SectionLocus

/-! # Comparison statements for the section trivialization locus -/

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace Langlands.SchemeModule

/-- A section trivializes on an open precisely when its stalk maps there are isomorphisms. -/
def LocalStalkCriterion : Prop :=
  ∀ (X : Scheme.{u}) (M : X.Modules) (s : GlobalSections M) (U : X.Opens),
    TrivializesOn M s U ↔ ∀ x ∈ U, IsStalkFrame M s x

/-- The trivialization open is the interior of the stalk-frame locus. -/
def TrivializationOpenInterior : Prop :=
  ∀ (X : Scheme.{u}) (M : X.Modules) (s : GlobalSections M),
    (trivializationOpen M s : Set X) = interior {x | IsStalkFrame M s x}

/-- The section trivializes precisely on the subopens of its trivialization open. -/
def MaximalTrivialization : Prop :=
  ∀ (X : Scheme.{u}) (M : X.Modules) (s : GlobalSections M) (U : X.Opens),
    TrivializesOn M s U ↔ U ≤ trivializationOpen M s

/-- The general stalk, topological and maximality comparisons for a section's locus. -/
def SectionLocusComparison : Prop :=
  LocalStalkCriterion.{u} ∧ TrivializationOpenInterior.{u} ∧ MaximalTrivialization.{u}

end Langlands.SchemeModule
