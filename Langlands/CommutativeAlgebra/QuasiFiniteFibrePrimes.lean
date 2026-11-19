import Mathlib.RingTheory.ZariskisMainTheorem
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.RingHom.QuasiFinite
import Mathlib.RingTheory.Spectrum.Prime.Jacobson

/-! # Primes witnessing the failure of quasi-finiteness -/

namespace Langlands.CommutativeAlgebra.QuasiFiniteFibrePrimes

open Topology

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- A finite-type algebra that is quasi-finite at every prime is quasi-finite. -/
theorem quasiFinite_of_forall_quasiFiniteAt [Algebra.FiniteType R S]
    (h : ∀ (q : Ideal S) [q.IsPrime], Algebra.QuasiFiniteAt R q) :
    Algebra.QuasiFinite R S := by
  rw [Algebra.QuasiFinite.iff_finite_comap_preimage_singleton]
  intro x
  have : CompactSpace (PrimeSpectrum.comap (algebraMap R S) ⁻¹' {x}) :=
    (PrimeSpectrum.preimageHomeomorphFiber R S x).symm.compactSpace
  have : DiscreteTopology (PrimeSpectrum.comap (algebraMap R S) ⁻¹' {x}) := by
    rw [discreteTopology_iff_isOpen_singleton]
    rintro ⟨q, hq⟩
    have hopen := (Algebra.quasiFiniteAt_iff_isOpen_singleton_fiber q).mp (h q.asIdeal)
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hq
    subst hq
    exact hopen
  exact Set.finite_coe_iff.mp finite_of_compact_of_discrete

/-- A finite-type algebra that is not quasi-finite fails to be quasi-finite at some
maximal ideal. -/
theorem exists_isMaximal_not_quasiFiniteAt [Algebra.FiniteType R S]
    (h : ¬ Algebra.QuasiFinite R S) :
    ∃ (M : Ideal S) (_ : M.IsMaximal), ¬ Algebra.QuasiFiniteAt R M := by
  by_contra! H
  apply h
  refine quasiFinite_of_forall_quasiFiniteAt fun q _ => ?_
  obtain ⟨M, hM, hqM⟩ := Ideal.exists_le_maximal q (Ideal.IsPrime.ne_top ‹_›)
  have := H M hM
  exact Algebra.QuasiFiniteAt.of_le hqM

/-- If a maximal ideal `M` of a finite-type algebra is the only prime below it in its
fibre, then the algebra is quasi-finite at `M`. -/
theorem quasiFiniteAt_of_forall_le [Algebra.FiniteType R S] (M : Ideal S) [M.IsMaximal]
    (h : ∀ q : Ideal S, q.IsPrime → q ≤ M → q.comap (algebraMap R S) = M.comap (algebraMap R S) →
      q = M) :
    Algebra.QuasiFiniteAt R M := by
  let m : PrimeSpectrum S := ⟨M, inferInstance⟩
  change Algebra.QuasiFiniteAt R m.asIdeal
  rw [Algebra.quasiFiniteAt_iff_isOpen_singleton_fiber]
  set p := PrimeSpectrum.comap (algebraMap R S) m
  let e := PrimeSpectrum.preimageHomeomorphFiber R S p
  have hmem : m ∈ PrimeSpectrum.comap (algebraMap R S) ⁻¹' {p} := rfl
  rw [← e.isOpen_image, Set.image_singleton]
  have : IsNoetherianRing (p.asIdeal.Fiber S) :=
    Algebra.FiniteType.isNoetherianRing p.asIdeal.ResidueField _
  have : IsJacobsonRing (p.asIdeal.Fiber S) :=
    isJacobsonRing_of_finiteType (A := p.asIdeal.ResidueField)
  let x : PrimeSpectrum (p.asIdeal.Fiber S) := e ⟨m, hmem⟩
  have key := (PrimeSpectrum.isOpen_singleton_tfae_of_isNoetherian_of_isJacobsonRing x).out 1 3
  refine key.mpr ⟨?_, ?_⟩
  · rw [← Set.image_singleton, e.isClosed_image]
    have hm : IsClosed ({m} : Set (PrimeSpectrum S)) :=
      (PrimeSpectrum.isClosed_singleton_iff_isMaximal m).mpr ‹_›
    convert hm.preimage continuous_subtype_val using 1
    ext ⟨z, hz⟩
    simp [Subtype.ext_iff]
  · intro y z hzy hy
    rw [Set.mem_singleton_iff] at hy ⊢
    subst hy
    obtain ⟨⟨z, hz⟩, rfl⟩ := e.surjective z
    have h1 : (⟨z, hz⟩ : PrimeSpectrum.comap (algebraMap R S) ⁻¹' {p}) ⤳ ⟨m, hmem⟩ :=
      e.isInducing.specializes_iff.mp hzy
    rw [subtype_specializes_iff, ← PrimeSpectrum.le_iff_specializes] at h1
    have h2 : z = m :=
      PrimeSpectrum.ext (h z.asIdeal inferInstance h1 (congrArg PrimeSpectrum.asIdeal hz))
    subst h2
    rfl

/-- The preimage of a maximal ideal under a homomorphism of algebras over a field, with
finite-type target, is maximal. -/
theorem isMaximal_comap_of_finiteType {K A B : Type*} [Field K] [CommRing A] [CommRing B]
    [Algebra K A] [Algebra K B] [Algebra.FiniteType K B] (f : A →ₐ[K] B) (M : Ideal B)
    [M.IsMaximal] : (M.comap f).IsMaximal := by
  let _ : Field (B ⧸ M) := Ideal.Quotient.field M
  have : Module.Finite K (B ⧸ M) := finite_of_finite_type_of_isJacobsonRing K (B ⧸ M)
  let g : A →ₐ[K] B ⧸ M := (Ideal.Quotient.mkₐ K M).comp f
  have hker : RingHom.ker g = M.comap f := by
    ext a
    simp [g, Ideal.Quotient.eq_zero_iff_mem]
  have hfield : IsField g.range := Subalgebra.isField_of_algebraic g.range
  have e := Ideal.quotientKerEquivRange g
  rw [← hker]
  exact Ideal.Quotient.maximal_of_isField _ (e.toMulEquiv.isField hfield)

/-- If a finite-type algebra is not quasi-finite, then some prime ideal lies strictly
below a maximal ideal with the same contraction. -/
theorem exists_lt_isMaximal_comap_eq [Algebra.FiniteType R S] (h : ¬ Algebra.QuasiFinite R S) :
    ∃ q M : Ideal S, q.IsPrime ∧ M.IsMaximal ∧ q < M ∧
      q.comap (algebraMap R S) = M.comap (algebraMap R S) := by
  obtain ⟨M, hM, hnot⟩ := exists_isMaximal_not_quasiFiniteAt h
  by_contra! H
  apply hnot
  refine quasiFiniteAt_of_forall_le M fun q hq hle hcomap => ?_
  by_contra hne
  exact H q M hq hM (lt_of_le_of_ne hle hne) hcomap

/-- A homomorphism of algebras over a field, with finite-type target, that is not
quasi-finite has a non-maximal prime ideal in the target whose contraction is maximal. -/
theorem exists_isPrime_not_isMaximal_of_not_quasiFinite {K A B : Type*} [Field K] [CommRing A]
    [CommRing B] [Algebra K A] [Algebra K B] [Algebra.FiniteType K B] (f : A →ₐ[K] B)
    (h : ¬ f.toRingHom.QuasiFinite) :
    ∃ q : Ideal B, q.IsPrime ∧ ¬ q.IsMaximal ∧ (q.comap f).IsMaximal := by
  let _ : Algebra A B := f.toRingHom.toAlgebra
  have hft : f.toRingHom.FiniteType := by
    refine RingHom.FiniteType.of_comp_finiteType (f := algebraMap K A) ?_
    rw [AlgHom.toRingHom_eq_coe, f.comp_algebraMap, RingHom.finiteType_algebraMap]
    infer_instance
  have : Algebra.FiniteType A B := hft
  obtain ⟨q, M, hq, hM, hlt, hcomap⟩ := exists_lt_isMaximal_comap_eq (R := A) (S := B) h
  refine ⟨q, hq, fun hqmax => hlt.ne (hqmax.eq_of_le hM.ne_top hlt.le), ?_⟩
  have hcomap' : q.comap f = M.comap f := hcomap
  rw [hcomap']
  exact isMaximal_comap_of_finiteType f M

end Langlands.CommutativeAlgebra.QuasiFiniteFibrePrimes
