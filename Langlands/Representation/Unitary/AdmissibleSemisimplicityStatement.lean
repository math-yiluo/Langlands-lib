import Langlands.Representation.Smooth.Definitions
import Langlands.Representation.Unitary.Basic
import Mathlib.RepresentationTheory.Semisimple

/-!
# Algebraic semisimplicity of admissible unitarizable representations

Compact open subgroups must be cofinal among open subgroups. The carrier is
an arbitrary algebraic complex module; no Hilbert completion is assumed.
-/

namespace Langlands

universe uG uV

/-- An admissible representation with an invariant positive Hermitian form
is algebraically semisimple when compact open subgroups are cofinal. -/
def AdmissibleUnitarySemisimplicityStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G],
    (∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G,
      IsCompact (L : Set G) ∧ L ≤ K) →
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (ρ : Representation ℂ G V),
      IsAdmissible ρ → IsUnitarizable ρ →
      Representation.IsSemisimpleRepresentation ρ

end Langlands
