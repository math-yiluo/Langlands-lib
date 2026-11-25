module

public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Tactic.CrossRefAttribute

set_option autoImplicit false
set_option maxSynthPendingDepth 3

/-!
# Standard open coverings of a prime spectrum

A *standard open covering* of a standard open `D(f)` in the prime spectrum of a commutative
ring is a finite family of elements whose standard opens have supremum `D(f)`; taking `f = 1`
gives a standard open covering of the whole spectrum.

This file collects the basic facts about such coverings. A standard open is covered by a
family of standard opens exactly when the covering elements generate the unit ideal after
localizing away from it, every open cover of a standard open admits a finite refinement by
standard opens, and a containment `D(g) ≤ D(f)` is witnessed both by a divisibility relation
between a power of `g` and `f` and by the invertibility of `f` after localizing away from `g`.

## Main definitions

* `PrimeSpectrum.IsStandardOpenCover`: a finite family of elements whose standard opens cover a
  specified standard open.
* `PrimeSpectrum.IsStandardOpenCoverOfSpectrum`: the specialization to the whole spectrum.

## Main results

* `PrimeSpectrum.basicOpen_le_iSup_iff_span_algebraMap_eq_top`: a standard open is contained in
  a union of standard opens exactly when the latter generate the unit ideal in its localization.
* `PrimeSpectrum.exists_finite_basicOpen_refinement`: every open cover of a standard open has a
  finite refinement by standard opens.
* `PrimeSpectrum.exists_pow_eq_mul_of_basicOpen_le`: a containment of standard opens makes a
  positive power of one element a multiple of the other.

## References

* [Stacks Project, Tag 01HS](https://stacks.math.columbia.edu/tag/01HS)
* [Stacks Project, Tag 01HT](https://stacks.math.columbia.edu/tag/01HT)
-/

@[expose] public section

open TopologicalSpace

namespace PrimeSpectrum

universe u v w

/-- Every open cover of a standard open in the prime spectrum has a finite
refinement by standard opens. -/
@[stacks 01HS "finite_standard_refinement"]
lemma exists_finite_basicOpen_refinement {R : Type u} [CommSemiring R]
    {ι : Type*} (f : R) (U : ι → Opens (PrimeSpectrum R))
    (hU : PrimeSpectrum.basicOpen f ≤ ⨆ i, U i) :
    ∃ (n : ℕ) (g : Fin n → R) (a : Fin n → ι),
      PrimeSpectrum.basicOpen f = ⨆ j, PrimeSpectrum.basicOpen (g j) ∧
        ∀ j, PrimeSpectrum.basicOpen (g j) ≤ U (a j) := by
  let β := Σ i, {g : R // PrimeSpectrum.basicOpen g ≤ U i ∧
    PrimeSpectrum.basicOpen g ≤ PrimeSpectrum.basicOpen f}
  have hcov : (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) ⊆
      ⋃ b : β, (PrimeSpectrum.basicOpen b.2.1 : Set (PrimeSpectrum R)) := by
    intro p hp
    obtain ⟨i, hpi⟩ := Opens.mem_iSup.mp (hU hp)
    obtain ⟨v, hvb, hpv, hvU⟩ :=
      PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
        (show p ∈ U i ⊓ PrimeSpectrum.basicOpen f from ⟨hpi, hp⟩)
        ((U i ⊓ PrimeSpectrum.basicOpen f).isOpen)
    obtain ⟨g, rfl⟩ := hvb
    exact Set.mem_iUnion.mpr ⟨⟨i, ⟨g, hvU.trans inf_le_left,
      hvU.trans inf_le_right⟩⟩, hpv⟩
  obtain ⟨t, ht⟩ := (PrimeSpectrum.isCompact_basicOpen f).elim_finite_subcover
      (fun b : β ↦ (PrimeSpectrum.basicOpen b.2.1 : Set (PrimeSpectrum R)))
      (fun b ↦ (PrimeSpectrum.basicOpen b.2.1).isOpen) hcov
  let φ : Fin t.card → β := fun j ↦ t.equivFin.symm j
  refine ⟨t.card, fun j ↦ (φ j).2.1, fun j ↦ (φ j).1, ?_, ?_⟩
  · apply le_antisymm
    · intro p hp
      obtain ⟨b, hbt, hpb⟩ := Set.mem_iUnion₂.mp (ht hp)
      refine Opens.mem_iSup.mpr ⟨t.equivFin ⟨b, hbt⟩, ?_⟩
      have hφg : (φ (t.equivFin ⟨b, hbt⟩)).2.1 = b.2.1 :=
        congrArg (fun x : β ↦ x.2.1) (by simp [φ])
      change p ∈ (PrimeSpectrum.basicOpen ((φ (t.equivFin ⟨b, hbt⟩)).2.1) :
        Set (PrimeSpectrum R))
      rwa [hφg]
    · intro p hp
      obtain ⟨j, hpj⟩ := Opens.mem_iSup.mp hp
      exact (φ j).2.2.2 hpj
  · exact fun j ↦ (φ j).2.2.1

end PrimeSpectrum

end
