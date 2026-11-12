import Langlands.Representation.Compact.UnitarySquareIntegrableStatements
import Langlands.Representation.Aubert.General.JacquetMultiplicityIrreducibility
import Langlands.Representation.Smooth.Schur.Proof
import Langlands.Topology.LocallyProfiniteProof

/-! # Renard IV.2.2, Corollary (i) -/

noncomputable section

universe u v

namespace Langlands.Renard.CompactRepresentation

/-- Renard IV.2.2, Corollary (i), with the exact published hypotheses. -/
theorem unitaryAdmissibleEndomorphism : UnitaryAdmissibleEndomorphismStatement.{u, v} := by
  intro G _ _ _ _ _ _ _ π hadm hunit
  have hcof : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G,
      IsCompact (L : Set G) ∧ L ≤ K := by
    intro K
    exact ((Topology.LocallyProfiniteProof.vanDantzig G).mp
      Topology.isLocallyProfinite_of_mathlib).2 K K.mem_nhds_one
  constructor
  · intro hdim
    have hnontrivial : Nontrivial π := by
      by_contra h
      let : Subsingleton π := not_nontrivial_iff_subsingleton.mp h
      have : Subsingleton (π.representation.IntertwiningMap π.representation) :=
        ⟨fun f g => by ext x; exact Subsingleton.elim _ _⟩
      have hz : Module.finrank ℂ (π.representation.IntertwiningMap π.representation) = 0 :=
        Module.finrank_zero_of_subsingleton
      omega
    let := hnontrivial
    exact Aubert.General.isIrreducible_of_semisimple_rank_endomorphism_le_one π
      (admissibleUnitarySemisimplicity G hcof π π.representation hadm hunit)
      (Module.rank_eq_one_iff_finrank_eq_one.mpr hdim).le
  · intro hirr
    obtain ⟨e⟩ := admissibleSchur_homEquiv π.representation hadm hirr
      π.representation (Representation.Equiv.refl π.representation)
    simpa using e.finrank_eq

end Langlands.Renard.CompactRepresentation
