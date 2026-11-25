/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Algebra.Regular.SMul
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.Algebra.Polynomial.Derivation
import Mathlib.RingTheory.RegularLocalRing.Polynomial
import WeilConjectures.RingTheory.Derivation.CompletionAndLocalization
import WeilConjectures.RingTheory.RootAlgebraRegularAtRoot
import WeilConjectures.RingTheory.RegularRingNormal
import WeilConjectures.RingTheory.FiniteProductNormal
import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs

/-! # Normality of full root algebras along a regular divisor

## References

* Stacks Project, Tag 0EYH, local ring verification in its proof
* Stacks Project, Tag 0EYG, the full root algebra in the strictly henselian calculation
* Stacks Project, Tag 07PF (Jacobian criterion)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- If `R` is regular and the derivative of `P` is not in the prime `q` of `R[X] / (P)`, then
the localization at `q` is a regular local ring. -/
private theorem regular_root_localization_of_derivative_not_mem
    (R : Type u) [CommRing R] [IsRegularRing R] (P : Polynomial R)
    (q : Ideal (Polynomial R ⧸ Ideal.span {P})) [q.IsPrime]
    (hd : Ideal.Quotient.mk (Ideal.span {P}) P.derivative ∉ q) :
    IsRegularLocalRing (Localization.AtPrime q) := by
  let I := Ideal.span ({P} : Set (Polynomial R))
  let p := q.comap (Ideal.Quotient.mk I)
  have hp : p.IsPrime := Ideal.comap_isPrime _ q
  let L := Localization.AtPrime p
  let a := algebraMap (Polynomial R) L
  let D : Derivation ℤ (Polynomial R) (Polynomial R) :=
    (Polynomial.derivative' (R := R)).restrictScalars ℤ
  have hP : P ∈ p := by
    change Ideal.Quotient.mk I P ∈ q
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self P)]
    exact q.zero_mem
  have hDP : D P ∉ p := hd
  obtain ⟨Dl, hDl, -, -⟩ :=
    (D.exists_completion_and_unique_localization (Polynomial R)).2 p.primeCompl
  have hx : a P ∈ IsLocalRing.maximalIdeal L :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff L p P).mpr hP
  have hDx : IsUnit (Dl (a P)) := by
    rw [hDl]
    exact (IsLocalization.AtPrime.isUnit_to_map_iff L p (D P)).mpr hDP
  have hx2 : a P ∉ IsLocalRing.maximalIdeal L ^ 2 := by
    intro h
    rw [pow_two] at h
    have hd' : Dl (a P) ∈ IsLocalRing.maximalIdeal L := by
      refine Submodule.mul_induction_on h ?_ ?_
      · intro x hx y hy
        rw [Dl.leibniz]
        exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hx) (Ideal.mul_mem_right _ _ hy)
      · intro x y hx hy
        rw [map_add]
        exact Ideal.add_mem _ hx hy
    exact (IsLocalRing.mem_maximalIdeal _).mp hd' hDx
  obtain ⟨hloc, hreg, -⟩ := IsRegularLocalRing.quotient_span_singleton hx hx2
  have hmap : I.map a = Ideal.span ({a P} : Set L) := by
    rw [Ideal.map_span, Set.image_singleton]
  have : IsRegularLocalRing (L ⧸ I.map a) := by
    rw [hmap]
    exact hreg
  have hcompl : Algebra.algebraMapSubmonoid (Polynomial R ⧸ I) p.primeCompl = q.primeCompl :=
    Ideal.map_primeCompl_comap_of_surjective (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective q
  have : IsLocalization q.primeCompl (L ⧸ I.map a) := by
    rw [← hcompl]
    infer_instance
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv q.primeCompl (L ⧸ I.map a)
      (Localization.AtPrime q)).toRingEquiv

/-- Full root models of a regular divisor have normal domain stalks. -/
theorem regular_divisor_root_model_normal
    (R : CommRingCat.{u}) [IsRegularRing R] (m : ℕ) (f : R)
    (hf : IsSMulRegular R f) [IsRegularRing (R ⧸ Ideal.span {f})]
    (e : Fin m → ℕ) (he : ∀ k, 0 < e k ∧ IsUnit (e k : R)) :
    let N := Spec (CommRingCat.of (∀ k : Fin m,
      AdjoinRoot ((Polynomial.X : Polynomial R) ^ e k - Polynomial.C f)))
    ∀ z : N, IsDomain (N.presheaf.stalk z) ∧
      IsIntegrallyClosed (N.presheaf.stalk z) := by
  dsimp only
  let B (k : Fin m) :=
    AdjoinRoot ((Polynomial.X : Polynomial R) ^ e k - Polynomial.C f)
  have hB (k : Fin m) : IsRegularRing (B k) := by
    apply isRegularRing_iff.mpr
    intro q hq
    by_cases ht : AdjoinRoot.root
        ((Polynomial.X : Polynomial R) ^ e k - Polynomial.C f) ∈ q
    · exact AdjoinRoot.isRegularLocalRing_atPrime_of_root_mem R f hf (e k) (he k).1 q ht
    · apply regular_root_localization_of_derivative_not_mem R _ q
      simp only [Polynomial.derivative_sub, Polynomial.derivative_X_pow,
        Polynomial.derivative_C, sub_zero, map_mul, map_pow]
      intro h
      have hunit : IsUnit (AdjoinRoot.of
          ((Polynomial.X : Polynomial R) ^ e k - Polynomial.C f) (e k : R)) :=
        (he k).2.map (AdjoinRoot.of _)
      have hpow : AdjoinRoot.root
          ((Polynomial.X : Polynomial R) ^ e k - Polynomial.C f) ^ (e k - 1) ∈ q :=
        (hq.mem_or_mem h).resolve_left (Ideal.notMem_of_isUnit q hunit)
      exact ht (hq.mem_of_pow_mem _ hpow)
  intro z
  obtain ⟨hd, hc⟩ := Pi.isNormalRing_of_finite B
    (fun k => by
      have : IsRegularRing (B k) := hB k
      exact IsRegularRing.isNormalRing (B k)) z.asIdeal
  let iso := Spec.stalkIso (CommRingCat.of (∀ k : Fin m, B k)) z
  let eqv := iso.commRingCatIsoToRingEquiv
  exact ⟨eqv.toMulEquiv.isDomain_iff.mpr hd, IsIntegrallyClosed.of_equiv eqv.symm⟩

end AlgebraicGeometry.Scheme
