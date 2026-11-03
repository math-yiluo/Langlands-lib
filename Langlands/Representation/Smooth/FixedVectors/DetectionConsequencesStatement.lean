import Langlands.Representation.Category.Subquotients
import Langlands.Representation.Filtration.ObjectDefinitions
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Basic.Complex.Basic

/-! # Generation and length from compact-open irreducible detection -/

set_option autoImplicit false

namespace Langlands

/-- Detecting irreducible actual subquotients by compact-open fixed vectors
detects every nonzero subquotient, forces generation of all subquotients by
those fixed vectors, and bounds length when the ambient fixed space is finite. -/
def CompactOpenDetectionConsequencesStatement.{uG, uV} : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (A : SmoothRep.{0, uG, uV} ℂ G) (K : OpenSubgroup G),
    IsCompact (K : Set G) →
    (∀ D : SmoothRep.{0, uG, uV} ℂ G,
      D.IsIrreducible → SmoothRep.IsSubquotient D A →
        ∃ v : D, v ∈ fixedVectors D.representation K.toSubgroup ∧ v ≠ 0) →
    (∀ D : SmoothRep.{0, uG, uV} ℂ G,
      SmoothRep.IsSubquotient D A → Nontrivial D →
        ∃ v : D, v ∈ fixedVectors D.representation K.toSubgroup ∧ v ≠ 0) ∧
    (∀ D : SmoothRep.{0, uG, uV} ℂ G,
      SmoothRep.IsSubquotient D A →
        ∀ S : Subrepresentation D.representation,
          fixedVectors D.representation K.toSubgroup ≤ S.toSubmodule → S = ⊤) ∧
    (∀ [FiniteDimensional ℂ (fixedVectors A.representation K.toSubgroup)],
      HasCompositionLengthAtMost A.obj
        (Module.finrank ℂ (fixedVectors A.representation K.toSubgroup)) ∧
        A.HasFiniteLength)

end Langlands
