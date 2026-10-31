import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.UniqueFactorizationDomain.GCDMonoid
import Mathlib.Tactic.LinearCombination

/-!
# Factoriality descends along flat local homomorphisms

If `R → S` is a flat local homomorphism of local rings and `S` is a unique factorization
domain, then so is `R`.
-/

namespace Langlands.CommutativeAlgebra

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- Divisibility reflects along a faithfully flat algebra. -/
theorem dvd_of_algebraMap_dvd_of_faithfullyFlat [Module.FaithfullyFlat R S] {a b : R}
    (h : algebraMap R S a ∣ algebraMap R S b) : a ∣ b := by
  have hI := Ideal.comap_map_eq_self_of_faithfullyFlat (B := S) (Ideal.span {a})
  rw [← Ideal.mem_span_singleton, ← hI, Ideal.mem_comap, Ideal.map_span, Set.image_singleton,
    Ideal.mem_span_singleton]
  exact h

/-- Over a flat algebra, a common multiple in `S` of the images of `a` and `b` is an
`S`-linear combination of images of common multiples of `a` and `b` in `R`. -/
theorem exists_common_multiples_of_flat [Module.Flat R S] {a b : R} {s t : S}
    (h : algebraMap R S a * s = algebraMap R S b * t) :
    ∃ (k : ℕ) (z : Fin k → R) (y : Fin k → S), (∀ j, a ∣ z j ∧ b ∣ z j) ∧
      algebraMap R S a * s = ∑ j, algebraMap R S (z j) * y j := by
  obtain ⟨k, c, y, hx, hc⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero (M := S)
    (f := ![a, -b]) (x := ![s, t]) (by simp [Fin.sum_univ_two, Algebra.smul_def, h])
  refine ⟨k, fun j => a * c 0 j, y, fun j => ⟨dvd_mul_right _ _, ?_⟩, ?_⟩
  · have hj := hc j
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at hj
    exact ⟨c 1 j, by linear_combination hj⟩
  · have h0 := hx 0
    simp only [Matrix.cons_val_zero] at h0
    rw [h0]
    simp [Finset.mul_sum, Algebra.smul_def, mul_assoc]

/-- **Descent of factoriality.** If `R → S` is a flat local homomorphism of local rings and
`S` is a unique factorization monoid, then `R` is a unique factorization monoid. -/
theorem uniqueFactorizationMonoid_of_flat_of_isLocalHom [IsLocalRing R] [IsLocalRing S]
    [Module.Flat R S] [IsLocalHom (algebraMap R S)] [UniqueFactorizationMonoid S] :
    UniqueFactorizationMonoid R := by
  classical
  have : Module.FaithfullyFlat R S := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have : IsDomain S := {}
  have hinj : Function.Injective (algebraMap R S) := FaithfulSMul.algebraMap_injective R S
  have : IsDomain R := hinj.isDomain (algebraMap R S)
  have hwf : WfDvdMonoid R := by
    refine Subrelation.wf (r := InvImage DvdNotUnit (algebraMap R S)) ?_
      (InvImage.wf _ wellFounded_dvdNotUnit)
    intro a b ⟨ha, x, hx, hb⟩
    refine ⟨fun h0 => ha (hinj (by simpa using h0)), algebraMap R S x,
      fun hu => hx (isUnit_of_map_unit _ _ hu), ?_⟩
    simp [hb]
  have hgcd : IsGCDMonoid R := by
    refine isGCDMonoid_iff_exists_lcm.mpr ⟨inferInstance, fun a b => ?_⟩
    by_cases hab : a = 0 ∨ b = 0
    · refine ⟨0, fun d => ⟨fun ⟨had, hbd⟩ => ?_, fun h0 => ?_⟩⟩
      · rcases hab with rfl | rfl
        · exact had
        · exact hbd
      · rcases hab with rfl | rfl
        · exact ⟨h0, (dvd_zero b).trans h0⟩
        · exact ⟨(dvd_zero a).trans h0, h0⟩
    push Not at hab
    obtain ⟨L, hL⟩ := (isGCDMonoid_iff_exists_lcm.mp (inferInstance : IsGCDMonoid S)).2
      (algebraMap R S a) (algebraMap R S b)
    have hL0 : L ≠ 0 := by
      rintro rfl
      have h := (hL (algebraMap R S a * algebraMap R S b)).1
        ⟨dvd_mul_right _ _, dvd_mul_left _ _⟩
      rw [zero_dvd_iff, ← map_mul, map_eq_zero_iff _ hinj] at h
      exact mul_ne_zero hab.1 hab.2 h
    obtain ⟨s, hs⟩ := ((hL L).2 dvd_rfl).1
    obtain ⟨t, ht⟩ := ((hL L).2 dvd_rfl).2
    obtain ⟨k, z, y, hz, hsum⟩ := exists_common_multiples_of_flat (hs.symm.trans ht)
    -- each `z j` is a multiple of `L` in `S`
    have hzL : ∀ j, L ∣ algebraMap R S (z j) := fun j =>
      (hL _).1 ⟨map_dvd _ (hz j).1, map_dvd _ (hz j).2⟩
    choose c hc using hzL
    have hone : ∑ j, c j * y j = 1 := by
      apply mul_left_cancel₀ hL0
      rw [mul_one, Finset.mul_sum]
      conv_rhs => rw [hs, hsum]
      exact Finset.sum_congr rfl fun j _ => by rw [hc j, mul_assoc]
    -- some `c j` is a unit, since `S` is local
    obtain ⟨j, hj⟩ : ∃ j, IsUnit (c j) := by
      by_contra hno
      push Not at hno
      have hmem : ∑ j, c j * y j ∈ IsLocalRing.maximalIdeal S :=
        sum_mem fun j _ => Ideal.mul_mem_right _ _
          ((IsLocalRing.mem_maximalIdeal _).mpr (hno j))
      rw [hone] at hmem
      exact (IsLocalRing.maximalIdeal.isMaximal S).ne_top
        ((Ideal.eq_top_iff_one _).mpr hmem)
    refine ⟨z j, fun d => ⟨fun ⟨had, hbd⟩ => ?_, fun hzd => ⟨(hz j).1.trans hzd,
      (hz j).2.trans hzd⟩⟩⟩
    apply dvd_of_algebraMap_dvd_of_faithfullyFlat (S := S)
    rw [hc j]
    exact hj.mul_right_dvd.mpr ((hL _).1 ⟨map_dvd _ had, map_dvd _ hbd⟩)
  exact ufm_of_decomposition_of_wfDvdMonoid

end Langlands.CommutativeAlgebra
