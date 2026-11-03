import Langlands.Representation.Smooth.FixedVectors.Definitions
import Langlands.Representation.Filtration.LengthCriterionStatement
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Finiteness.Defs

/-!
# Algebraic fixed-vector reductions for Howe's finite-length implication

These are internal proposition targets. They separate the elementary generator
and chain arguments from the reductive-group subquotient-detection theorem.
-/

set_option autoImplicit false

noncomputable section

namespace Langlands

/-- Smooth finite group-algebra generation has a finite generating family
fixed by one open subgroup. Fixed vectors for every smaller subgroup still
generate the representation. No topological-group assumption is needed. -/
def CommonFixedGeneratorsStatement.{uR, uG, uV} : Prop :=
  ∀ (R : Type uR) [CommRing R] (G : Type uG) [Group G] [TopologicalSpace G]
    (V : Type uV) [AddCommGroup V] [Module R V] (ρ : Representation R G V),
    IsSmooth ρ → Module.Finite (MonoidAlgebra R G) ρ.asModule →
      ∃ (n : ℕ) (v : Fin n → V) (K : OpenSubgroup G),
        Submodule.span (MonoidAlgebra R G)
          (Set.range (fun i => ρ.asModuleEquiv.symm (v i))) = ⊤ ∧
        (∀ i, v i ∈ fixedVectors ρ K.toSubgroup) ∧
        ∀ (L : Subgroup G), L ≤ K.toSubgroup →
          ∀ S : Subrepresentation ρ, fixedVectors ρ L ≤ S.toSubmodule → S = ⊤

/-- If every strict inclusion of invariant subspaces is witnessed by a vector
fixed by `K`, finite dimension of the ambient fixed-vector space bounds actual
composition length and implies finite length over the actual group algebra.
No smoothness or topology is needed. -/
def FixedVectorsStrictInclusionLengthStatement.{uR, uG, uV} : Prop :=
  ∀ (R : Type uR) [Field R] (G : Type uG) [Group G]
    (V : Type uV) [AddCommGroup V] [Module R V]
    (ρ : Representation R G V) (K : Subgroup G),
    ∀ [FiniteDimensional R (fixedVectors ρ K)],
      (∀ S T : Subrepresentation ρ, S < T →
        ∃ v : V, v ∈ T ∧ v ∈ fixedVectors ρ K ∧ v ∉ S) →
      HasCompositionLengthAtMost (Rep.of ρ) (Module.finrank R (fixedVectors ρ K)) ∧
        IsFiniteLength (MonoidAlgebra R G) ρ.asModule

/-- The two elementary fixed-vector reductions, with independent coefficient,
group and representation-carrier universes. -/
def FixedVectorLengthReductionStatement.{uR, uG, uV} : Prop :=
  CommonFixedGeneratorsStatement.{uR, uG, uV} ∧
    FixedVectorsStrictInclusionLengthStatement.{uR, uG, uV}

end Langlands
