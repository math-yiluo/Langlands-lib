/-
Ported from `P2M/Sol/S_PrimeSpectrum_eq_univ_of_isOpen_of_nonempty_of_forall_isMaximal.lean` of the Anthropic FLT formalization,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2. Copyright 2026 Anthropic, PBC.
Licensed under Apache License 2.0; see licenses/Anthropic-FLT/LICENSE, NOTICE,
and ATTRIBUTION.md. Imports are prefixed; utility commands are replaced by
standard Lean commands. See the paired Markdown for changes and provenance.
-/
import Mathlib
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PrimeSpectrum_eq_univ_of_isOpen_of_nonempty_of_forall_isMaximal

set_option autoImplicit false

open scoped TensorProduct

universe u v w

theorem solution
    {A : Type u} [CommRing A] [IsJacobsonRing A]
    (U : Set (PrimeSpectrum A)) (hU : IsOpen U) (hne : U.Nonempty)
    (htrans : ∀ P Q : PrimeSpectrum A, P.asIdeal.IsMaximal → Q.asIdeal.IsMaximal → P ∈ U → Q ∈ U) :
    U = Set.univ := by
  classical
  obtain ⟨P, hP⟩ := hne
  obtain ⟨s, hs⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus _).mp (isClosed_compl_iff.mpr hU)

  have hPnot : ¬ (s ⊆ (P.asIdeal : Set A)) := by
    intro h
    have : P ∈ Uᶜ := by rw [hs]; exact (PrimeSpectrum.mem_zeroLocus _ _).mpr h
    exact this hP
  rw [Set.not_subset] at hPnot
  obtain ⟨f, hfs, hfP⟩ := hPnot

  have hfrad : f ∉ (⊥ : Ideal A).radical := fun h => hfP (by
    have h' : f ∈ nilradical A := h
    exact nilradical_le_prime P.asIdeal h')
  rw [Ideal.radical_eq_jacobson, Ideal.jacobson, Submodule.mem_sInf] at hfrad
  push_neg at hfrad
  obtain ⟨M, ⟨-, hM⟩, hfM⟩ := hfrad
  have hMU : (⟨M, hM.isPrime⟩ : PrimeSpectrum A) ∈ U := by
    by_contra h
    have h' : (⟨M, hM.isPrime⟩ : PrimeSpectrum A) ∈ Uᶜ := h
    rw [hs, PrimeSpectrum.mem_zeroLocus] at h'
    exact hfM (h' hfs)

  apply Set.eq_univ_of_forall
  intro Q
  by_contra hQ
  have hQz : s ⊆ (Q.asIdeal : Set A) := by
    have h' : Q ∈ Uᶜ := hQ
    rw [hs, PrimeSpectrum.mem_zeroLocus] at h'
    exact h'
  obtain ⟨M', hM', hQM'⟩ := Q.asIdeal.exists_le_maximal Q.isPrime.ne_top
  have hM'U : (⟨M', hM'.isPrime⟩ : PrimeSpectrum A) ∈ U :=
    htrans ⟨M, hM.isPrime⟩ ⟨M', hM'.isPrime⟩ hM hM' hMU
  have hM'c : (⟨M', hM'.isPrime⟩ : PrimeSpectrum A) ∈ Uᶜ := by
    rw [hs, PrimeSpectrum.mem_zeroLocus]
    intro a ha
    exact hQM' (hQz ha)
  exact hM'c hM'U
