import Langlands.Representation.Smooth.RenardSchurStatements
import Langlands.Representation.Smooth.Contragredient.AdmissibleDualityProof
import Langlands.Representation.Smooth.Contragredient.LawsProof
import Langlands.Topology.LocallyProfiniteProof

/-! # Admissibility characterized by smooth biduality -/

noncomputable section

universe u v

namespace Langlands.Renard.Smooth

/-- Even an arbitrary linear equivalence with the full algebraic double dual
forces a complex vector space to be finite dimensional. -/
theorem finiteDimensional_of_bidual_equiv
    {V : Type v} [AddCommGroup V] [Module ℂ V]
    (e : V ≃ₗ[ℂ] Module.Dual ℂ (Module.Dual ℂ V)) : FiniteDimensional ℂ V := by
  rw [FiniteDimensional, ← Module.rank_lt_aleph0_iff]
  by_contra! h
  have h₁ : Module.rank ℂ V < Module.rank ℂ (Module.Dual ℂ V) := by
    simpa using lift_rank_lt_rank_dual h
  have h₂ : Module.rank ℂ (Module.Dual ℂ V) <
      Module.rank ℂ (Module.Dual ℂ (Module.Dual ℂ V)) := by
    simpa using lift_rank_lt_rank_dual (le_trans h h₁.le)
  exact (ne_of_lt (lt_trans h₁ h₂)) e.rank_eq

/-- Fixed vectors in an equivalent smooth bidual are algebraically reflexive
in dimension, so cofinal compact-open fixed spaces are finite dimensional. -/
theorem isAdmissible_of_smooth_bidual_equiv
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {V : Type v} [AddCommGroup V] [Module ℂ V]
    (hcof : ∀ H : OpenSubgroup G, ∃ K : OpenSubgroup G,
      IsCompact (K : Set G) ∧ K ≤ H)
    (π : Representation ℂ G V) (hπ : IsSmooth π)
    (e : π.Equiv (smoothContragredient (smoothContragredient π))) :
    IsAdmissible π := by
  apply (isAdmissible_iff_of_cofinal {K | IsCompact (K : Set G)} hcof).2
  refine ⟨hπ, ?_⟩
  intro K hK
  let a := LinearEquiv.ofBijective (smoothDualFixedRestriction π K.toSubgroup)
    (smoothDualFixedRestriction_bijective π hπ K hK)
  let b := LinearEquiv.ofBijective
    (smoothDualFixedRestriction (smoothContragredient π) K.toSubgroup)
    (smoothDualFixedRestriction_bijective (smoothContragredient π)
      (isSmooth_smoothContragredient π) K hK)
  exact finiteDimensional_of_bidual_equiv
    (((fixedVectorsEquiv e K.toSubgroup).trans b).trans a.symm.dualMap)

/-- Renard III.1.7, both canonical and arbitrary-equivalence formulations. -/
theorem admissibleBidual : AdmissibleBidualStatement.{u, v} := by
  intro G _ _ _ _ _ _ V _ _ π hπ
  have hcof : ∀ H : OpenSubgroup G, ∃ K : OpenSubgroup G,
      IsCompact (K : Set G) ∧ K ≤ H := fun H =>
    (Langlands.Topology.LocallyProfiniteProof.vanDantzig G).mp
      Langlands.Topology.isLocallyProfinite_of_mathlib |>.2 (H : Set G) H.mem_nhds_one
  have forward (ha : IsAdmissible π) : Function.Bijective (smoothBidual hπ) :=
    ⟨smoothBidual_injective_of_compact_cofinal hcof π hπ,
      smoothBidual_surjective_of_compact_cofinal hcof π ha⟩
  refine ⟨⟨forward, ?_⟩, ⟨fun ha => ⟨(smoothBidual hπ).ofBijective (forward ha)⟩, ?_⟩⟩
  · intro hb
    exact isAdmissible_of_smooth_bidual_equiv hcof π hπ
      ((smoothBidual hπ).ofBijective hb)
  · rintro ⟨e⟩
    exact isAdmissible_of_smooth_bidual_equiv hcof π hπ e

end Langlands.Renard.Smooth
