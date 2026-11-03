import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Spectrum.Prime.Jacobson
import Mathlib.RingTheory.Spectrum.Prime.ConstructibleSet
import Mathlib.RingTheory.Spectrum.Prime.Chevalley

/-! # Rational points of finitely generated algebras over an algebraically closed field -/

noncomputable section

open Topology

namespace Langlands.GroupScheme.KostantRosenlicht

section Nullstellensatz

variable {k : Type*} [Field k] [IsAlgClosed k] {A : Type*} [CommRing A] [Algebra k A]
  [Algebra.FiniteType k A]

/-- Hilbert's Nullstellensatz: every maximal ideal is the kernel of a `k`-point. -/
theorem exists_algHom_ker_eq (m : Ideal A) [m.IsMaximal] :
    ∃ χ : A →ₐ[k] k, RingHom.ker χ = m := by
  let := Ideal.Quotient.field m
  have : Module.Finite k (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing k (A ⧸ m)
  have hb := IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := A ⧸ m)
  let eq : k ≃ₐ[k] A ⧸ m := AlgEquiv.ofBijective (Algebra.ofId k _) hb
  refine ⟨eq.symm.toAlgHom.comp (Ideal.Quotient.mkₐ k m), ?_⟩
  ext a
  simp [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]

/-- On a reduced finitely generated algebra, a function vanishing at every `k`-point is zero. -/
theorem eq_zero_of_forall_algHom [IsReduced A] {a : A} (h : ∀ χ : A →ₐ[k] k, χ a = 0) :
    a = 0 := by
  have : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := k)
  have hj : a ∈ (⊥ : Ideal A).jacobson := by
    refine Submodule.mem_sInf.mpr fun J hJ => ?_
    have : Ideal.IsMaximal J := hJ.2
    obtain ⟨χ, hχ⟩ := exists_algHom_ker_eq (k := k) J
    rw [← hχ]
    exact h χ
  rw [← Ideal.radical_eq_jacobson] at hj
  obtain ⟨n, hn⟩ := hj
  exact IsNilpotent.eq_zero ⟨n, (Submodule.mem_bot _).mp hn⟩

end Nullstellensatz

/-- In the spectrum of a Jacobson ring, a constructible set without closed points is empty. -/
theorem eq_empty_of_isConstructible {R : Type*} [CommRing R] [IsJacobsonRing R]
    {s : Set (PrimeSpectrum R)} (hs : IsConstructible s)
    (h : ∀ x ∈ s, ¬ x.asIdeal.IsMaximal) : s = ∅ := by
  obtain ⟨S, rfl⟩ := PrimeSpectrum.exists_constructibleSetData_iff.mpr hs
  rw [Set.eq_empty_iff_forall_notMem]
  intro x hx
  have hx' := hx
  simp only [PrimeSpectrum.ConstructibleSetData.toSet, Set.mem_iUnion] at hx'
  obtain ⟨C, hC, hxC⟩ := hx'
  have hlc : IsLocallyClosed C.toSet := by
    rw [PrimeSpectrum.BasicConstructibleSetData.toSet, Set.sdiff_eq]
    exact (PrimeSpectrum.isClosed_zeroLocus _).isLocallyClosed.inter
      (PrimeSpectrum.isClosed_zeroLocus _).isOpen_compl.isLocallyClosed
  obtain ⟨y, hy, hy'⟩ := nonempty_inter_closedPoints ⟨x, hxC⟩ hlc
  refine h y ?_ ((PrimeSpectrum.isClosed_singleton_iff_isMaximal y).mp hy')
  simp only [PrimeSpectrum.ConstructibleSetData.toSet, Set.mem_iUnion]
  exact ⟨C, hC, hy⟩

end Langlands.GroupScheme.KostantRosenlicht
