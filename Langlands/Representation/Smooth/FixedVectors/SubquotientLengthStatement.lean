import Langlands.Representation.Smooth.FixedVectors.Definitions
import Langlands.Representation.Filtration.LengthCriterionProof
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Basic.Complex.Basic

/-! Compact-open exactness bridges for actual successive subquotients. -/

set_option autoImplicit false

noncomputable section

namespace Langlands

/-- A nonzero compact-open fixed vector in an actual strict successive
subquotient lifts to an ambient fixed vector in the upper subrepresentation
and outside the lower one. -/
def CompactOpenSubquotientFixedVectorStatement.{uG, uV} : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V),
    IsSmooth ρ → ∀ (K : OpenSubgroup G), IsCompact (K : Set G) →
      ∀ S T : Subrepresentation ρ, S < T →
        Nontrivial (fixedVectors (LengthCriterionProof.quotientRep S T) K.toSubgroup) →
        ∃ v : V, v ∈ T ∧ v ∈ fixedVectors ρ K.toSubgroup ∧ v ∉ S

/-- Compact-open fixed vectors detecting each nonzero strict successive
subquotient bound actual composition length by the ambient fixed dimension
and imply actual group-algebra finite length. -/
def CompactOpenSubquotientLengthStatement.{uG, uV} : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V),
    IsSmooth ρ → ∀ (K : OpenSubgroup G), IsCompact (K : Set G) →
      ∀ [FiniteDimensional ℂ (fixedVectors ρ K.toSubgroup)],
        (∀ S T : Subrepresentation ρ, S < T →
          Nontrivial (fixedVectors (LengthCriterionProof.quotientRep S T) K.toSubgroup)) →
        HasCompositionLengthAtMost (Rep.of ρ)
          (Module.finrank ℂ (fixedVectors ρ K.toSubgroup)) ∧
          IsFiniteLength (MonoidAlgebra ℂ G) ρ.asModule

/-- Exactness and the resulting fixed-vector length reduction, with
independent group and representation-carrier universes. -/
def CompactOpenSubquotientLengthReductionStatement.{uG, uV} : Prop :=
  CompactOpenSubquotientFixedVectorStatement.{uG, uV} ∧
    CompactOpenSubquotientLengthStatement.{uG, uV}

end Langlands
