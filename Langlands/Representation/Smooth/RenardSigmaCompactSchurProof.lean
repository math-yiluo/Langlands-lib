import Langlands.Representation.Smooth.RenardSchurStatements
import Langlands.Representation.Schur.CountableDimensionProof
import Langlands.Representation.OrbitSpan
import Mathlib.Topology.Compactness.SigmaCompact

/-! # Schur's lemma for sigma-compact groups -/

noncomputable section

universe u v w

namespace Langlands.Renard.Smooth

/-- The orbit of a smooth vector in a sigma-compact group is countable. -/
theorem sigmaCompact_countable_orbit
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SigmaCompactSpace G] {V : Type v} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ G V) {x : V} (hx : IsSmoothVector π x) :
    (Set.range fun g => π g x).Countable := by
  let S (n : ℕ) : Set V := Set.range fun g : compactCovering G n => π g.val x
  have hS (n : ℕ) : (S n).Finite := by
    let : CompactSpace (compactCovering G n) :=
      isCompact_iff_compactSpace.mp (isCompact_compactCovering G n)
    exact ((Hecke.orbitMap_locallyConstant π hx).comp_continuous
      continuous_subtype_val).range_finite
  apply (Set.countable_iUnion fun n => (hS n).countable).mono
  rintro _ ⟨g, rfl⟩
  obtain ⟨n, hn⟩ := exists_mem_compactCovering g
  exact Set.mem_iUnion.mpr ⟨n, ⟨⟨g, hn⟩, rfl⟩⟩

/-- A nonzero orbit spans an irreducible representation, so its rank is countable. -/
theorem sigmaCompact_irreducible_rank_le_aleph0
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SigmaCompactSpace G] {V : Type v} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ G V) (hπ : IsSmooth π) (hi : π.IsIrreducible) :
    Module.rank ℂ V ≤ Cardinal.aleph0 := by
  let := hi
  let : Nontrivial V := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) π.asModule
  obtain ⟨x, hx⟩ := exists_ne (0 : V)
  calc
    Module.rank ℂ V = Module.rank ℂ (⊤ : Submodule ℂ V) := (rank_top ℂ V).symm
    _ = Module.rank ℂ (Submodule.span ℂ (Set.range fun g => π g x)) := by
      rw [span_range_orbit_eq_top hi hx]
    _ ≤ Cardinal.mk (Set.range fun g => π g x) := rank_span_le _
    _ ≤ Cardinal.aleph0 := Cardinal.mk_le_aleph0_iff.mpr
      (sigmaCompact_countable_orbit π (hπ x)).to_subtype

/-- Renard III.1.8, with independent source and target carrier universes. -/
theorem sigmaCompactSchur : SigmaCompactSchurStatement.{u, v, w} := by
  intro G _ _ _ _ _ _ _ V _ _ π hπ hi
  constructor
  · intro f
    exact (countableDimensionalSchur π
      (sigmaCompact_irreducible_rank_le_aleph0 π hπ hi) hi f).exists
  · intro W _ _ τ _ hτ hne f
    let := hi
    let := hτ
    exact (Representation.IsIrreducible.bijective_or_eq_zero f).resolve_left
      (fun hf => hne.false (f.ofBijective hf))

end Langlands.Renard.Smooth
