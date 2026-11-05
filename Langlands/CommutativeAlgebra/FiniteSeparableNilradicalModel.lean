import Langlands.CommutativeAlgebra.FiniteSeparableLiftedPolynomialModel
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.Spectrum.Prime.Homeomorph
import Mathlib.RingTheory.QuasiFinite.Basic

/-! # The nilradical of an actual lifted finite free model -/

noncomputable section

universe u v w

open scoped TensorProduct
open Algebra Polynomial

namespace Langlands.CommutativeAlgebra

/-- Tensoring with an actual coefficient quotient kills precisely its extended ideal. -/
theorem ker_includeRight_quotient (R : Type u) (A : Type v)
    [CommRing R] [CommRing A] [Algebra R A] (I : Ideal R) :
    RingHom.ker (Algebra.TensorProduct.includeRight :
      A →ₐ[R] (R ⧸ I) ⊗[R] A).toRingHom = I.map (algebraMap R A) := by
  let e := Algebra.TensorProduct.quotIdealMapEquivQuotTensor A I
  have he : (Algebra.TensorProduct.includeRight :
      A →ₐ[R] (R ⧸ I) ⊗[R] A).toRingHom =
      e.toRingHom.comp (Ideal.Quotient.mk (I.map (algebraMap R A))) := by
    ext a
    exact (Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk A I a).symm
  rw [he, RingHom.ker_equiv_comp]
  exact Ideal.mk_ker

variable (R : Type u) (K : Type v) (L : Type w)
  [CommRing R] [IrreducibleSpace (PrimeSpectrum R)] [Field K] [Field L]

local instance nilradicalIsPrime : (nilradical R).IsPrime :=
  PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical.mp inferInstance

variable [Algebra (R ⧸ nilradical R) K] [IsFractionRing (R ⧸ nilradical R) K]
  [Algebra (R ⧸ nilradical R) L] [Algebra K L]
  [IsScalarTower (R ⧸ nilradical R) K L]

/-- The model is the actual monic quotient over the original irreducible ring. -/
abbrev FiniteSeparableNilradicalModel :=
  FiniteSeparableLiftedPolynomialModel R (R ⧸ nilradical R) K L

/-- Construct the lifted model over an arbitrary irreducible affine base. -/
def finiteSeparableNilradicalModel
    [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    FiniteSeparableNilradicalModel R K L :=
  finiteSeparableLiftedPolynomialModel R (R ⧸ nilradical R) K L
    Ideal.Quotient.mk_surjective

namespace FiniteSeparableNilradicalModel

variable {R K L}

omit [IrreducibleSpace (PrimeSpectrum R)]
/-- Coefficient reduction has exactly the extended nilradical as its kernel. -/
theorem ker_reductionMap (d : FiniteSeparableNilradicalModel R K L) :
    RingHom.ker d.reductionMap = (nilradical R).map (algebraMap R d.Carrier) := by
  rw [FiniteSeparableLiftedPolynomialModel.reductionMap, RingHom.ker_equiv_comp]
  exact ker_includeRight_quotient R d.Carrier (nilradical R)

/-- The reduced domain model is the actual reduction of the lifted quotient. -/
theorem ker_reductionMap_eq_nilradical (d : FiniteSeparableNilradicalModel R K L) :
    RingHom.ker d.reductionMap = nilradical d.Carrier := by
  apply le_antisymm
  · rw [ker_reductionMap]
    simpa only [nilradical, Ideal.zero_eq_bot, Ideal.map_bot] using
      (Ideal.map_radical_le (f := algebraMap R d.Carrier) (I := (⊥ : Ideal R)))
  · have := RingHom.ker_isPrime d.reductionMap
    exact nilradical_le_prime _

/-- The actual reduction of the lifted ring is the original domain subalgebra. -/
def reducedEquiv (d : FiniteSeparableNilradicalModel R K L) :
    d.Carrier ⧸ nilradical d.Carrier ≃+* d.quotientModel.Carrier :=
  (Ideal.quotEquivOfEq d.ker_reductionMap_eq_nilradical.symm).trans
    (d.reductionMap.quotientKerEquivOfSurjective
      (d.reductionMap_surjective Ideal.Quotient.mk_surjective))

@[simp]
theorem reducedEquiv_mk (d : FiniteSeparableNilradicalModel R K L) (a : d.Carrier) :
    d.reducedEquiv (Ideal.Quotient.mk _ a) = d.reductionMap a := by
  simp [reducedEquiv]

/-- Coefficient reduction induces a homeomorphism of the actual prime spectra. -/
theorem isHomeomorph_reduction (d : FiniteSeparableNilradicalModel R K L) :
    IsHomeomorph (PrimeSpectrum.comap d.reductionMap) := by
  apply PrimeSpectrum.isHomeomorph_comap
  · intro x
    obtain ⟨a, rfl⟩ := d.reductionMap_surjective Ideal.Quotient.mk_surjective x
    exact ⟨1, by decide, by simp⟩
  · exact d.ker_reductionMap_eq_nilradical.le

/-- The lifted model has an irreducible spectrum even when it has nilpotents. -/
theorem irreducibleSpectrum (d : FiniteSeparableNilradicalModel R K L) :
    IrreducibleSpace (PrimeSpectrum d.Carrier) := by
  apply PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical.mpr
  rw [← d.ker_reductionMap_eq_nilradical]
  exact RingHom.ker_isPrime d.reductionMap

/-- The actual generic prime of the lifted quotient. -/
def genericPrime (d : FiniteSeparableNilradicalModel R K L) : PrimeSpectrum d.Carrier :=
  ⟨RingHom.ker d.reductionMap, RingHom.ker_isPrime d.reductionMap⟩

@[simp]
theorem genericPrime_asIdeal (d : FiniteSeparableNilradicalModel R K L) :
    d.genericPrime.asIdeal = nilradical d.Carrier :=
  d.ker_reductionMap_eq_nilradical

/-- This prime is generic for the whole spectrum. -/
theorem isGenericPoint_genericPrime (d : FiniteSeparableNilradicalModel R K L) :
    IsGenericPoint d.genericPrime Set.univ := by
  rw [IsGenericPoint, PrimeSpectrum.closure_singleton, d.genericPrime_asIdeal]
  exact (PrimeSpectrum.zeroLocus_eq_univ_iff _).mpr (fun _ h => h)

/-- Its contraction is the prime nilradical of the original base. -/
theorem genericPrime_under (d : FiniteSeparableNilradicalModel R K L) :
    d.genericPrime.asIdeal.under R = nilradical R := by
  ext r
  change d.reductionMap (AdjoinRoot.of d.polynomial r) = 0 ↔ r ∈ nilradical R
  rw [d.reductionMap_of]
  have hinj : Function.Injective (algebraMap (R ⧸ nilradical R) d.quotientModel.Carrier) :=
    algebraMap_injective_of_field_isFractionRing
      (R ⧸ nilradical R) d.quotientModel.Carrier K L
  rw [map_eq_zero_iff _ hinj]
  exact Ideal.Quotient.eq_zero_iff_mem

/-- The generic prime is the unique prime over the generic prime of the base. -/
theorem prime_eq_genericPrime (d : FiniteSeparableNilradicalModel R K L)
    (q : PrimeSpectrum d.Carrier) (hq : q.asIdeal.under R = nilradical R) :
    q = d.genericPrime := by
  apply PrimeSpectrum.ext
  apply Eq.symm
  apply Algebra.QuasiFinite.eq_of_le_of_under_eq (R := R)
  · rw [d.genericPrime_asIdeal]
    exact nilradical_le_prime _
  · exact d.genericPrime_under.trans hq.symm

end FiniteSeparableNilradicalModel

end Langlands.CommutativeAlgebra
