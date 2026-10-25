import Langlands.Representation.Smooth.Definitions
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Topology.Algebra.Group.Subgroup

/-!
# Uniform finite expansion of central action operators

This proposition combines finite-generator evaluation on admissible fixed
spaces with the finite-operator-span expansion used in JPS (1979), p.181.
It is an internal derived statement, not a proof or a character decomposition.
-/

namespace Langlands

universe uG uA uV

/-- An admissible finitely generated complex representation has a uniform
finite expansion along every continuous homomorphism into its actual center.
The coefficient functions are continuous with finite-dimensional left-translate
span, and the coefficient operators belong to the actual central action span. -/
def CentralOperatorExpansionStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (A : Type uA) [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A]
    (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (c : A →* Subgroup.center G),
    Continuous c → IsAdmissible ρ →
    Module.Finite (MonoidAlgebra ℂ G) ρ.asModule →
    ∃ (X : Finset (A → ℂ)) (T : (A → ℂ) → Module.End ℂ V),
      (∀ χ ∈ X, Continuous χ ∧
        FiniteDimensional ℂ (Submodule.span ℂ
          (Set.range fun b : A => fun a : A => χ (b * a)))) ∧
      (∀ χ ∈ X, T χ ∈ Submodule.span ℂ
        (Set.range fun a : A => ρ ((c a : Subgroup.center G) : G))) ∧
      ∀ a : A, ρ ((c a : Subgroup.center G) : G) = ∑ χ ∈ X, χ a • T χ

end Langlands
