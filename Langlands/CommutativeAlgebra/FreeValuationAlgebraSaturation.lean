import Mathlib.RingTheory.Valuation.ValuationRing
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.Algebra.Module.Torsion.Free

/-! # Scalar saturation in free valuation algebras -/

noncomputable section

universe u v w

namespace Langlands.CommutativeAlgebra

variable {R : Type u} [CommRing R] [IsDomain R] [ValuationRing R]

/-- A primitive scalar normalization, including a linear functional witnessing
the primitivity of the normalized vector. -/
structure ScalarNormalization (R : Type u) [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M] (x : M) where
  scalar : R
  vector : M
  functional : M →ₗ[R] R
  scalar_ne_zero : scalar ≠ 0
  eq_smul : x = scalar • vector
  functional_vector : functional vector = 1

private theorem exists_coordinate_dvd {ι : Type w} (c : ι → R)
    (s : Finset ι) (hs : s.Nonempty) :
    ∃ i ∈ s, ∀ j ∈ s, c i ∣ c j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp at hs
  | @insert a s ha ih =>
    by_cases h : s.Nonempty
    · obtain ⟨i, hi, hdiv⟩ := ih h
      rcases ValuationRing.dvd_total (c a) (c i) with hai | hia
      · refine ⟨a, Finset.mem_insert_self _ _, ?_⟩
        intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact dvd_refl _
        · exact hai.trans (hdiv j hj)
      · refine ⟨i, Finset.mem_insert_of_mem hi, ?_⟩
        intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact hia
        · exact hdiv j hj
    · have hzero : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
      subst s
      exact ⟨a, by simp, by simp⟩

/-- Every nonzero vector of a free module over a valuation domain is a
nonzero scalar multiple of a vector on which a linear functional takes value one. -/
theorem exists_scalar_normalization_of_free
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Free R M]
    {x : M} (hx : x ≠ 0) :
    ∃ (r : R) (y : M) (l : M →ₗ[R] R), r ≠ 0 ∧ x = r • y ∧ l y = 1 := by
  classical
  let b := Module.Free.chooseBasis R M
  let c := b.repr x
  have hc : c ≠ 0 := by
    intro h
    exact hx (b.repr.injective (by simpa [c] using h))
  obtain ⟨i, hi, hdiv⟩ := exists_coordinate_dvd (fun j => c j) c.support
    (Finsupp.support_nonempty_iff.mpr hc)
  have hci : c i ≠ 0 := Finsupp.mem_support_iff.mp hi
  have hd (j) : c i ∣ c j := by
    by_cases hj : j ∈ c.support
    · exact hdiv j hj
    · simp [Finsupp.notMem_support_iff.mp hj]
  choose d hd using hd
  let d' : Module.Free.ChooseBasisIndex R M →₀ R :=
    Finsupp.onFinset c.support d (by
      intro j hj
      apply Finsupp.mem_support_iff.mpr
      rw [hd j]
      exact mul_ne_zero hci hj)
  have he : c = c i • d' := by
    ext j
    exact hd j
  refine ⟨c i, b.repr.symm d', b.coord i, hci, ?_, ?_⟩
  · apply b.repr.injective
    simpa [c] using he
  · rw [Module.Basis.coord_repr_symm]
    change d i = 1
    apply mul_left_cancel₀ hci
    simpa using (hd i).symm

/-- Choose actual primitive normalization data for a nonzero vector of a free
module over a valuation domain. No uniqueness or canonicity is asserted. -/
noncomputable def scalarNormalizationOfFree
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Free R M]
    {x : M} (hx : x ≠ 0) : ScalarNormalization R M x :=
  Classical.choice (by
    obtain ⟨r, y, l, hr, hxy, hl⟩ := exists_scalar_normalization_of_free (R := R) hx
    exact ⟨⟨r, y, l, hr, hxy, hl⟩⟩)

/-- The normalized vector is outside the maximal-ideal multiple of the free module. -/
theorem exists_scalar_normalization_not_mem
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Free R M]
    {x : M} (hx : x ≠ 0) :
    ∃ (r : R) (y : M), r ≠ 0 ∧ x = r • y ∧
      y ∉ IsLocalRing.maximalIdeal R • (⊤ : Submodule R M) := by
  let n := scalarNormalizationOfFree (R := R) hx
  refine ⟨n.scalar, n.vector, n.scalar_ne_zero, n.eq_smul, ?_⟩
  intro hy
  have hm := Submodule.smul_top_le_comap_smul_top
    (IsLocalRing.maximalIdeal R) n.functional hy
  change n.functional n.vector ∈ IsLocalRing.maximalIdeal R • (⊤ : Ideal R) at hm
  rw [Ideal.smul_eq_mul, Ideal.mul_top, n.functional_vector] at hm
  exact hm isUnit_one

variable {A : Type v} [CommRing A] [Algebra R A] [Module.Free R A]

/-- In a free valuation algebra with integral closed fibre, multiplication by an
element nonzero on that fibre preserves and reflects divisibility by a base scalar. -/
theorem scalar_dvd_iff_mul_dvd_of_free_of_closedFibrePrime
    (hp : ((IsLocalRing.maximalIdeal R).map (algebraMap R A)).IsPrime)
    {s a : A} (hs : s ∉ (IsLocalRing.maximalIdeal R).map (algebraMap R A)) (r : R) :
    algebraMap R A r ∣ s * a ↔ algebraMap R A r ∣ a := by
  constructor
  · rintro ⟨z, hz⟩
    by_cases ha : a = 0
    · simp [ha]
    obtain ⟨d, a₀, hd, hnorm, ha₀⟩ := exists_scalar_normalization_not_mem (R := R) ha
    have ha₀' : a₀ ∉ (IsLocalRing.maximalIdeal R).map (algebraMap R A) := by
      rw [Ideal.smul_top_eq_map] at ha₀
      exact ha₀
    rcases ValuationRing.dvd_total r d with hrd | hdr
    · obtain ⟨t, ht⟩ := hrd
      refine ⟨t • a₀, ?_⟩
      rw [hnorm, ht, mul_smul, Algebra.smul_def]
    · obtain ⟨t, ht⟩ := hdr
      have hcancel : t • z = s * a₀ := by
        apply smul_right_injective A hd
        calc
          d • (t • z) = algebraMap R A r * z := by rw [← mul_smul, ← ht, Algebra.smul_def]
          _ = s * a := hz.symm
          _ = d • (s * a₀) := by rw [hnorm, mul_smul_comm]
      have htunit : IsUnit t := by
        by_contra h
        have htm : t ∈ IsLocalRing.maximalIdeal R := h
        have hm : t • z ∈ (IsLocalRing.maximalIdeal R).map (algebraMap R A) := by
          rw [Algebra.smul_def]
          exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ htm)
        rw [hcancel] at hm
        exact (hp.mem_or_mem hm).elim hs ha₀'
      obtain ⟨t', htt'⟩ := htunit.exists_right_inv
      refine ⟨t' • a₀, ?_⟩
      rw [← Algebra.smul_def, ht, mul_smul, smul_smul t t', htt', one_smul]
      exact hnorm
  · intro h
    exact dvd_mul_of_dvd_right h _

end Langlands.CommutativeAlgebra
