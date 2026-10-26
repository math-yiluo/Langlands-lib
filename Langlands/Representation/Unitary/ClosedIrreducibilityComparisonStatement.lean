import Langlands.Representation.Smooth.Definitions
import Langlands.Representation.Unitary.Basic
import Langlands.Representation.Archimedean.SmoothVectors
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Closed and algebraic irreducibility for an admissible positive form

This internal comparison concerns an arbitrary dense, equivariant,
form-preserving embedding into a normed inner-product representation.
It does not construct a completion or prove irreducibility of an induction.
-/

namespace Langlands

universe uG uV uH

/-- Closed irreducibility of a normed realization implies algebraic
irreducibility of the admissible smooth representation that embeds densely
and preserves its positive invariant form. -/
def AdmissibleClosedIrreducibilityComparisonStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G],
    (∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G,
      IsCompact (L : Set G) ∧ L ≤ K) →
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (ρ : Representation ℂ G V),
      IsAdmissible ρ →
      ∀ (b : InvariantPositiveForm ρ)
        (H : Type uH) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
        (π : G →* (H →L[ℂ] H)) (j : V →ₗ[ℂ] H),
        DenseRange j →
        (∀ (g : G) (v : V), j (ρ g v) = π g (j v)) →
        (∀ (v w : V), inner ℂ (j v) (j w) = b.inner v w) →
        Archimedean.IsTopologicallyIrreducible π →
        Representation.IsIrreducible ρ

end Langlands
