import Langlands.Representation.Smooth.Definitions
import Langlands.Representation.Unitary.Basic
import Mathlib.RepresentationTheory.Irreducible

/-!
# Scalar comparison of arbitrary invariant sesquilinear forms

A derived form of admissible Schur's lemma. No symmetry or nondegeneracy
assumption is placed on the sesquilinear form.
-/

namespace Langlands

universe uG uV

/-- Every nonzero invariant sesquilinear form on an irreducible admissible
unitarizable representation is a nonzero complex scalar multiple of any
chosen invariant positive form. -/
def InvariantSesquilinearScalarStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G],
    (∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G,
      IsCompact (L : Set G) ∧ L ≤ K) →
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (ρ : Representation ℂ G V),
      IsAdmissible ρ → ρ.IsIrreducible →
      ∀ (b : InvariantPositiveForm ρ) (B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ), B ≠ 0 →
        (∀ (g : G) (v w : V), B (ρ g v) (ρ g w) = B v w) →
        ∃ c : ℂ, c ≠ 0 ∧ ∀ v w : V, B v w = c * b.inner v w

end Langlands
