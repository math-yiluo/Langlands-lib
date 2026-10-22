import Langlands.Representation.Smooth.Definitions
import Mathlib.Basic.Complex.Basic
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Connected.TotallyDisconnected

/-!
# An admissible irreducible first-factor subrepresentation

This proposition definition states an internal prerequisite for the two-factor
existence clause of Flath's Theorem 1: an admissible irreducible smooth complex
representation of `G₁ × G₂` contains, as an actual subspace, an admissible
irreducible representation of `G₁` fixed by a compact open subgroup of `G₂`.
No truth of the proposition is asserted here.
-/

namespace Langlands

universe uG₁ uG₂ uV

/-- Every admissible irreducible complex representation `ρ` of a product of two
locally profinite groups has a subrepresentation `S` of its restriction
`ρ.comp (MonoidHom.inl G₁ G₂)` to the first factor such that `S` is
admissible and irreducible as a representation of `G₁`, and every vector of
`S` is fixed by `(1, k₂)` for every `k₂` in some compact open subgroup `K₂`
of `G₂`. -/
def AdmissibleProductFirstFactorSubrepresentationStatement : Prop :=
  ∀ (G₁ : Type uG₁) (G₂ : Type uG₂) [Group G₁] [Group G₂]
    [TopologicalSpace G₁] [TopologicalSpace G₂]
    [IsTopologicalGroup G₁] [IsTopologicalGroup G₂]
    [T2Space G₁] [T2Space G₂]
    [LocallyCompactSpace G₁] [LocallyCompactSpace G₂]
    [TotallyDisconnectedSpace G₁] [TotallyDisconnectedSpace G₂]
    (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (G₁ × G₂) V),
    IsAdmissible ρ → ρ.IsIrreducible →
    ∃ (S : Subrepresentation (ρ.comp (MonoidHom.inl G₁ G₂)))
      (K₂ : OpenSubgroup G₂),
      IsCompact (K₂ : Set G₂) ∧
      (∀ k₂ ∈ K₂, ∀ v ∈ S.toSubmodule, ρ (1, k₂) v = v) ∧
      IsAdmissible S.toRepresentation ∧ S.toRepresentation.IsIrreducible

end Langlands
