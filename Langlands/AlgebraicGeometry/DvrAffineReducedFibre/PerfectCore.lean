import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.Minpoly.Finite
import Mathlib.RingTheory.AlgebraicIndependent.Adjoin
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-! # The perfect core of a finitely generated field extension -/

open Polynomial

noncomputable section

namespace Langlands.AlgebraicGeometry.DvrAffineReducedFibre

private theorem variable_pow_sub_irreducible (k ι : Type*) [Field k] (i : ι)
    {n : ℕ} (hn : 0 < n) :
    Irreducible ((X : (FractionRing (MvPolynomial ι k))[X]) ^ n -
      C (algebraMap (MvPolynomial ι k) _ (MvPolynomial.X i))) := by
  classical
  let P := MvPolynomial ι k
  let t : P := MvPolynomial.X i
  let g : P[X] := X ^ n - C t
  let I : Ideal P := Ideal.span {t}
  have ht : Prime t := MvPolynomial.X_prime
  have hI : I.IsPrime := (Ideal.span_singleton_prime ht.ne_zero).mpr ht
  have hg : g.Monic := monic_X_pow_sub_C _ hn.ne'
  have hdegree : g.degree = n := degree_X_pow_sub_C hn t
  have hgi : Irreducible g := by
    apply irreducible_of_eisenstein_criterion hI
    · rw [hg.leadingCoeff]
      exact fun h => hI.ne_top (I.eq_top_of_isUnit_mem h isUnit_one)
    · intro j hj
      have hjn : j ≠ n := fun he => (lt_irrefl (n : WithBot ℕ)) (by
        simpa only [he, hdegree] using hj)
      have hc : g.coeff j = -(C t).coeff j := by simp [g, coeff_X_pow, hjn]
      rw [hc]
      by_cases hj0 : j = 0
      · subst j
        simpa only [coeff_C_zero, I, Ideal.neg_mem_iff] using Ideal.mem_span_singleton_self t
      · simp [coeff_C, hj0]
    · rw [hdegree]
      exact WithBot.coe_lt_coe.mpr hn
    · change g.coeff 0 ∉ (Ideal.span {t}) ^ 2
      have hc : g.coeff 0 = -t := by simp [g, coeff_X_pow, hn.ne]
      rw [hc, Ideal.neg_mem_iff, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      rintro ⟨r, hr⟩
      have heq : t * 1 = t * (t * r) := by simpa only [mul_one, pow_two, mul_assoc] using hr
      exact ht.not_isUnit (isUnit_iff_dvd_one.mpr
        ⟨r, (mul_right_injective₀ ht.ne_zero) heq⟩)
    · exact hg.isPrimitive
  have hm := (hg.irreducible_iff_irreducible_map_fraction_map
    (K := FractionRing P)).mp hgi
  simpa only [g, t, Polynomial.map_sub, Polynomial.map_pow, map_X, map_C] using hm

/-- An element with `p^n`th roots for every `n` in a finitely generated field
extension is algebraic over the base, when `p > 1`. -/
theorem isAlgebraic_of_exists_pow_eq {k L : Type*} [Field k] [Field L] [Algebra k L]
    [Algebra.EssFiniteType k L] {p : ℕ} (hp : 1 < p) {x : L}
    (hx : ∀ n : ℕ, ∃ y : L, y ^ p ^ n = x) : IsAlgebraic k x := by
  classical
  by_contra htrans
  have hsingle : AlgebraicIndepOn k id ({x} : Set L) :=
    (algebraicIndependent_singleton_iff (⟨x, Set.mem_singleton x⟩ : ({x} : Set L))).mpr htrans
  obtain ⟨s, hxs, hs⟩ := exists_isTranscendenceBasis_superset hsingle
  let i : s := ⟨x, hxs (Set.mem_singleton x)⟩
  let K := IntermediateField.adjoin k (Set.range ((↑) : s → L))
  have : Algebra.IsAlgebraic K L := hs.isAlgebraic_field
  have : Algebra.EssFiniteType K L := Algebra.EssFiniteType.of_comp k K L
  have : Module.Finite K L := Algebra.finite_of_essFiniteType_of_isAlgebraic
  let n := Module.finrank K L
  have hn : Module.finrank K L < p ^ n :=
    n.lt_two_pow_self.trans_le (Nat.pow_le_pow_left hp n)
  obtain ⟨y, hy⟩ := hx n
  let P := MvPolynomial s k
  let e : FractionRing P ≃ₐ[k] K := hs.1.aevalEquivField
  let t : K := e (algebraMap P (FractionRing P) (MvPolynomial.X i))
  have ht : algebraMap K L t = x := by
    change (e (algebraMap P (FractionRing P) (MvPolynomial.X i)) : L) = x
    rw [hs.1.aevalEquivField_algebraMap_apply_coe, MvPolynomial.aeval_X]
  have hP := variable_pow_sub_irreducible k s i (pow_pos (Nat.zero_lt_of_lt hp) n)
  have hq : Irreducible ((X : K[X]) ^ p ^ n - C t) := by
    have hm := (MulEquiv.irreducible_iff (Polynomial.mapAlgEquiv e)).mpr hP
    simp only [Polynomial.coe_mapAlgEquiv, Polynomial.map_sub, Polynomial.map_pow,
      map_X, map_C] at hm
    exact hm
  have hroot : aeval y ((X : K[X]) ^ p ^ n - C t) = 0 := by
    simp only [aeval_sub, map_pow, aeval_X, aeval_C, ht, hy, sub_self]
  have hmin : minpoly K y = (X : K[X]) ^ p ^ n - C t :=
    (minpoly.eq_of_irreducible_of_monic hq hroot
      (monic_X_pow_sub_C _ (pow_ne_zero _ (Nat.ne_zero_of_lt hp)))).symm
  have hbound := minpoly.natDegree_le (A := K) (B := L) (x := y)
  rw [hmin, natDegree_X_pow_sub_C] at hbound
  exact (not_lt_of_ge hbound) hn

/-- The intersection of the images of all Frobenius iterates in a field. -/
def perfectCore (L : Type*) [Field L] (p : ℕ) [ExpChar L p] : Subfield L :=
  ⨅ n : ℕ, (iterateFrobenius L p n).fieldRange

/-- For an essentially finite-type extension of an algebraically closed field,
the intersection of the Frobenius images in positive characteristic is the
image of the base. -/
theorem perfectCore_eq_fieldRange (k L : Type*) [Field k] [IsAlgClosed k] [Field L]
    [Algebra k L] [Algebra.EssFiniteType k L] {p : ℕ} [ExpChar L p] (hp : 1 < p) :
    perfectCore L p = (algebraMap k L).fieldRange := by
  ext x
  simp only [perfectCore, Subfield.mem_iInf, RingHom.mem_fieldRange, iterateFrobenius_def]
  constructor
  · intro hx
    have ha := isAlgebraic_of_exists_pow_eq (k := k) hp hx
    have hm : (minpoly k x).leadingCoeff = 1 := (minpoly.monic ha.isIntegral).leadingCoeff
    have hd := IsAlgClosed.degree_eq_one_of_irreducible k (minpoly.irreducible ha.isIntegral)
    have he := minpoly.aeval k x
    rw [eq_X_add_C_of_degree_eq_one hd, hm, C_1, one_mul, aeval_add, aeval_X, aeval_C,
      add_eq_zero_iff_eq_neg] at he
    exact ⟨-((minpoly k x).coeff 0), by rw [map_neg, ← he]⟩
  · rintro ⟨a, rfl⟩ n
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq a (pow_pos (Nat.zero_lt_of_lt hp) n)
    exact ⟨algebraMap k L z, by rw [← map_pow, hz]⟩

open IsLocalRing in
/-- The residue field at a prime of a finite-type algebra is finitely generated
over the base residue field when the map to the local ring is local. -/
theorem essFiniteType_residueField_atPrime (R B : Type*) [CommRing R] [IsLocalRing R]
    [CommRing B] [Algebra R B] [Algebra.FiniteType R B] (q : Ideal B) [q.IsPrime]
    [IsLocalHom (algebraMap R (Localization.AtPrime q))] :
    Algebra.EssFiniteType (ResidueField R) q.ResidueField := by
  have : Algebra.EssFiniteType (B ⧸ q) q.ResidueField :=
    Algebra.EssFiniteType.of_isLocalization _ (nonZeroDivisors (B ⧸ q))
  have : Algebra.EssFiniteType R q.ResidueField := Algebra.EssFiniteType.comp R (B ⧸ q) _
  exact Algebra.EssFiniteType.of_comp R (ResidueField R) _

open IsLocalRing in
/-- The perfect core at a vertical prime over an algebraically closed residue
field is precisely the image of the base residue field. -/
theorem perfectCore_eq_fieldRange_residueField_atPrime (R B : Type*) [CommRing R] [IsLocalRing R]
    [IsAlgClosed (ResidueField R)] [CommRing B] [Algebra R B] [Algebra.FiniteType R B]
    (q : Ideal B) [q.IsPrime] [IsLocalHom (algebraMap R (Localization.AtPrime q))]
    {p : ℕ} (hp : 1 < p) [ExpChar q.ResidueField p] :
    perfectCore q.ResidueField p = (algebraMap (ResidueField R) q.ResidueField).fieldRange := by
  have := essFiniteType_residueField_atPrime R B q
  exact perfectCore_eq_fieldRange (ResidueField R) q.ResidueField hp

end Langlands.AlgebraicGeometry.DvrAffineReducedFibre
