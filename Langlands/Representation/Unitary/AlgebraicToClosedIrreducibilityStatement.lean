import Langlands.Representation.Smooth.Definitions
import Langlands.Representation.Unitary.Basic
import Langlands.Representation.Archimedean.SmoothVectors
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Algebraic-to-closed irreducibility in an admissible Hilbert realization

This internal proposition compares an admissible algebraic representation with
an actual dense Hilbert realization preserving its invariant positive form.
It states a comparison and provides no proof or completion construction.
-/

namespace Langlands

universe uG uV uH

/-- An admissible algebraically irreducible representation has a topologically
irreducible dense Hilbert realization when the realization preserves its
actual invariant positive form. -/
def AdmissibleAlgebraicToClosedIrreducibilityStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G],
    (∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G,
      IsCompact (L : Set G) ∧ L ≤ K) →
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (ρ : Representation ℂ G V), IsAdmissible ρ →
      Representation.IsIrreducible ρ →
      ∀ (b : InvariantPositiveForm ρ)
        (H : Type uH) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
        (π : G →* (H →L[ℂ] H)) (j : V →ₗ[ℂ] H),
        DenseRange j →
        (∀ (g : G) (v : V), j (ρ g v) = π g (j v)) →
        (∀ (v w : V), inner ℂ (j v) (j w) = b.inner v w) →
        Archimedean.IsTopologicallyIrreducible π

end Langlands
