import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.IntegralClosure.GoingDown
import Mathlib.RingTheory.Localization.BaseChange

/-! # Generic fibres and integral extensions at vertical primes -/

open TensorProduct

noncomputable section

namespace Langlands.AlgebraicGeometry.DvrAffineReducedFibre

section FractionField

variable (R B : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra R B]
    [IsLocalHom (algebraMap R B)]

/-- In an injective local map of DVRs, inverting the nonzero elements of the
base inverts every nonzero element of the target. -/
theorem isFractionRing_tensor_of_localDvrMap (hinj : Function.Injective (algebraMap R B)) :
    IsFractionRing B (B ⊗[R] FractionRing R) := by
  let M := Algebra.algebraMapSubmonoid B (nonZeroDivisors R)
  have hle : M ≤ nonZeroDivisors B :=
    map_le_nonZeroDivisors_of_injective (algebraMap R B) hinj le_rfl
  have ht : IsLocalization M (B ⊗[R] FractionRing R) :=
    IsLocalization.tensor (FractionRing R) (nonZeroDivisors R)
  refine (IsLocalization.iff_of_le_of_exists_dvd M (nonZeroDivisors B) hle ?_).mp ht
  intro x hx
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible B
  obtain ⟨e, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
    ((map_ne_zero_iff _ hinj).mpr hπ.ne_zero) ht
  have he : 0 < e := by
    by_contra h
    have hunit : IsUnit (algebraMap R B π) := by
      simpa only [hu, Nat.eq_zero_of_not_pos h, pow_zero, mul_one] using u.isUnit
    exact hπ.not_isUnit (IsLocalHom.map_nonunit (f := algebraMap R B) _ hunit)
  obtain ⟨n, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
    (mem_nonZeroDivisors_iff_ne_zero.mp hx) ht
  refine ⟨algebraMap R B (π ^ n), ⟨π ^ n, mem_nonZeroDivisors_of_ne_zero (pow_ne_zero _ hπ.ne_zero),
    rfl⟩, ?_⟩
  have hdiv : t ^ n ∣ algebraMap R B (π ^ n) := by
    rw [map_pow, hu, mul_pow, ← pow_mul]
    exact dvd_mul_of_dvd_right (pow_dvd_pow t (Nat.le_mul_of_pos_left n he)) _
  exact (hv ▸ associated_unit_mul_left (t ^ n) (v : B) v.isUnit : Associated x (t ^ n))
    |>.dvd_iff_dvd_left.mpr hdiv

/-- The generic fibre of an injective local DVR extension is the fraction field
of the target DVR, with its target algebra structure. -/
def genericFibreFractionRingEquiv (hinj : Function.Injective (algebraMap R B)) :
    B ⊗[R] FractionRing R ≃ₐ[B] FractionRing B := by
  have := isFractionRing_tensor_of_localDvrMap R B hinj
  exact IsLocalization.algEquiv (nonZeroDivisors B) _ _

end FractionField

section GoingDown

variable (R S : Type*) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [CommRing S] [Algebra R S] [Algebra.IsIntegral R S]

/-- An integral algebra over a normal domain has going down if the image of
each nonzero scalar is regular. The algebra itself may have several components. -/
theorem hasGoingDown_of_regularScalars
    (hreg : Algebra.algebraMapSubmonoid S (nonZeroDivisors R) ≤ nonZeroDivisors S) :
    Algebra.HasGoingDown R S := by
  constructor
  intro p hp Q hQ hle
  obtain ⟨Q₀, h₀, h₀Q⟩ := Ideal.exists_minimalPrimes_le (I := ⊥) (J := Q) bot_le
  have : Q₀.IsPrime := h₀.isPrime
  let C := S ⧸ Q₀
  have hRC : Function.Injective (algebraMap R C) := by
    apply (injective_iff_map_eq_zero (algebraMap R C)).mpr
    intro r hr
    by_contra hn
    have hm : algebraMap R S r ∈ Q₀ := Ideal.Quotient.eq_zero_iff_mem.mp hr
    exact Set.disjoint_left.mp (Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes h₀) hm
      (hreg ⟨r, mem_nonZeroDivisors_of_ne_zero hn, rfl⟩)
  have : FaithfulSMul R C := (faithfulSMul_iff_algebraMap_injective R C).mpr hRC
  let f := Ideal.Quotient.mk Q₀
  let q := Q.map f
  have hker : RingHom.ker f ≤ Q := by simpa [f] using h₀Q
  have : q.IsPrime := Q.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hker
  have hq : q.comap f = Q :=
    (Q.comap_map_of_surjective f Ideal.Quotient.mk_surjective).trans (sup_eq_left.mpr hker)
  have hqR : q.under R = Q.under R := by
    calc
      q.under R = (q.under S).under R := (Ideal.under_under q).symm
      _ = Q.under R := congrArg (Ideal.under R) hq
  have := Algebra.HasGoingDown.exists_ideal_le_liesOver_of_lt (R := R) q (hqR.symm ▸ hle)
  obtain ⟨P, hP, hPrime, hPR⟩ := this
  refine ⟨P.comap f, (Ideal.comap_mono hP).trans_eq hq, inferInstance, ⟨?_⟩⟩
  change p = (P.under S).under R
  rw [Ideal.under_under]
  exact hPR.over

/-- A prime minimal over a principal ideal contracts to such a prime in the
normal domain under a regular-scalar integral map. -/
theorem minimalPrime_under_of_regularScalars
    (hreg : Algebra.algebraMapSubmonoid S (nonZeroDivisors R) ≤ nonZeroDivisors S)
    {r : R} (Q : Ideal S) [Q.IsPrime]
    (hQ : (Ideal.span {algebraMap R S r}).IsMinimalPrime Q) :
    (Ideal.span {r}).IsMinimalPrime (Q.under R) := by
  have : Algebra.HasGoingDown R S := hasGoingDown_of_regularScalars R S hreg
  refine ⟨⟨inferInstance, ?_⟩, ?_⟩
  · exact (Q.under R).span_singleton_le_iff_mem.mpr (hQ.le (Ideal.mem_span_singleton_self _))
  · intro p hp hle
    have : p.IsPrime := hp.1
    obtain ⟨P, hPle, hP, hPR⟩ := Ideal.exists_ideal_le_liesOver_of_le Q hle
    have hI : Ideal.span {algebraMap R S r} ≤ P := by
      apply P.span_singleton_le_iff_mem.mpr
      change r ∈ P.under R
      rw [← hPR.over]
      exact hp.2 (Ideal.mem_span_singleton_self r)
    have hQP : Q ≤ P := hQ.2 ⟨hP, hI⟩ hPle
    exact (Ideal.comap_mono hQP).trans_eq hPR.over.symm

end GoingDown

end Langlands.AlgebraicGeometry.DvrAffineReducedFibre
