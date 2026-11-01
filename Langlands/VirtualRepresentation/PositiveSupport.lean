import Langlands.VirtualRepresentation.EffectiveFixedVector

/-! Support control and effectivity reflection for positive integral maps. -/

noncomputable section

namespace Langlands.VirtualRepresentation

open scoped BigOperators

universe u v

variable {ι : Type u} {κ : Type v}

/-- Positivity controls support on an effective eigenvector; a positive map
with nonzero columns and a multiplicity-free image reflects effectivity on
the support of an effective vector. -/
def PositiveSupportStatement : Prop :=
  (∀ (L : IntegralLattice ι →ₗ[ℤ] IntegralLattice ι)
      (v : IntegralLattice ι), v ∈ effective →
      (∀ i ∈ v.support, L (generator i) ∈ effective) →
      ∀ (r : ℕ), L v = r • v →
      ∀ i ∈ v.support, (L (generator i)).support ⊆ v.support) ∧
  (∀ (J : IntegralLattice ι →ₗ[ℤ] IntegralLattice κ)
      (v : IntegralLattice ι), v ∈ effective →
      (∀ i ∈ v.support, J (generator i) ∈ effective) →
      (∀ i ∈ v.support, J (generator i) ≠ 0) →
      (∀ j, (J v) j ≤ 1) →
      ∀ (w : IntegralLattice ι), w.support ⊆ v.support →
      J w ∈ effective → w ∈ effective)

theorem linear_apply_coefficient
    (L : IntegralLattice ι →ₗ[ℤ] IntegralLattice κ)
    (v : IntegralLattice ι) (j : κ) :
    (L v) j = ∑ i ∈ v.support, v i * (L (generator i)) j := by
  classical
  have hexpand : v = ∑ i ∈ v.support, v i • generator i := by
    conv_lhs => rw [← Finsupp.sum_single v]
    apply Finset.sum_congr rfl
    intro i _
    simp [generator]
  conv_lhs => rw [hexpand, map_sum]
  simp only [Finsupp.finsetSum_apply, map_zsmul, Finsupp.smul_apply, zsmul_eq_mul,
    Int.cast_id]

theorem weighted_column_le
    (L : IntegralLattice ι →ₗ[ℤ] IntegralLattice κ)
    (v : IntegralLattice ι) (hv : v ∈ effective)
    (hpositive : ∀ i ∈ v.support, L (generator i) ∈ effective)
    (i : ι) (hi : i ∈ v.support) (j : κ) :
    v i * (L (generator i)) j ≤ (L v) j := by
  rw [linear_apply_coefficient L v j]
  exact Finset.single_le_sum (fun k hk => mul_nonneg (hv k) (hpositive k hk j)) hi

/-- A positive endomorphism that acts by a natural scalar on an effective
vector preserves the support of every constituent column. -/
theorem support_generator_image_subset_of_nonnegative_scalar
    (L : IntegralLattice ι →ₗ[ℤ] IntegralLattice ι)
    (v : IntegralLattice ι) (hv : v ∈ effective)
    (hpositive : ∀ i ∈ v.support, L (generator i) ∈ effective)
    (r : ℕ) (hscalar : L v = r • v)
    (i : ι) (hi : i ∈ v.support) :
    (L (generator i)).support ⊆ v.support := by
  classical
  intro j hj
  by_contra hjv
  have hz : v j = 0 := Finsupp.notMem_support_iff.mp hjv
  have hvi : 0 < v i := lt_of_le_of_ne (hv i)
    (Ne.symm (Finsupp.mem_support_iff.mp hi))
  have hcol : 0 < (L (generator i)) j := lt_of_le_of_ne (hpositive i hi j)
    (Ne.symm (Finsupp.mem_support_iff.mp hj))
  have hle := weighted_column_le L v hv hpositive i hi j
  have hzero : (L v) j = 0 := by simp [hscalar, hz]
  have hp := mul_pos hvi hcol
  omega

/-- If the positive weighted sum of columns is multiplicity-free, each
nonzero column has a coordinate isolating it from every other column. -/
theorem exists_isolating_coordinate
    (J : IntegralLattice ι →ₗ[ℤ] IntegralLattice κ)
    (v : IntegralLattice ι) (hv : v ∈ effective)
    (hpositive : ∀ i ∈ v.support, J (generator i) ∈ effective)
    (hfree : ∀ j, (J v) j ≤ 1)
    (i : ι) (hi : i ∈ v.support) (hne : J (generator i) ≠ 0) :
    ∃ j, (J (generator i)) j = 1 ∧
      ∀ k ∈ v.support, k ≠ i → (J (generator k)) j = 0 := by
  classical
  obtain ⟨j, hj⟩ := Finsupp.support_nonempty_iff.mpr hne
  have hvi : 0 < v i := lt_of_le_of_ne (hv i)
    (Ne.symm (Finsupp.mem_support_iff.mp hi))
  have hc : 0 < (J (generator i)) j := lt_of_le_of_ne (hpositive i hi j)
    (Ne.symm (Finsupp.mem_support_iff.mp hj))
  have hbound := (weighted_column_le J v hv hpositive i hi j).trans (hfree j)
  have hvione : v i = 1 := by
    have hm := le_mul_of_one_le_right (hv i) (show 1 ≤ (J (generator i)) j by omega)
    omega
  have hcone : (J (generator i)) j = 1 := by
    rw [hvione, one_mul] at hbound
    omega
  refine ⟨j, hcone, ?_⟩
  have hsum :
      ∑ k ∈ v.support.erase i, v k * (J (generator k)) j = 0 := by
    have h := Finset.sum_erase_add v.support
      (fun k => v k * (J (generator k)) j) hi
    rw [← linear_apply_coefficient, hvione, hcone, one_mul] at h
    have hnonneg : 0 ≤ ∑ k ∈ v.support.erase i, v k * (J (generator k)) j :=
      Finset.sum_nonneg fun k hk =>
        mul_nonneg (hv k) (hpositive k (Finset.mem_of_mem_erase hk) j)
    have hb := hfree j
    omega
  have heach := (Finset.sum_eq_zero_iff_of_nonneg
    (fun k hk => mul_nonneg (hv k)
      (hpositive k (Finset.mem_of_mem_erase hk) j))).mp hsum
  intro k hk hki
  have hz := heach k (Finset.mem_erase.mpr ⟨hki, hk⟩)
  exact (mul_eq_zero.mp hz).resolve_left (Finsupp.mem_support_iff.mp hk)

/-- A positive map with nonzero supported columns and multiplicity-free
total image reflects effectivity on the original support. -/
theorem effective_of_effective_image_on_support
    (J : IntegralLattice ι →ₗ[ℤ] IntegralLattice κ)
    (v : IntegralLattice ι) (hv : v ∈ effective)
    (hpositive : ∀ i ∈ v.support, J (generator i) ∈ effective)
    (hnonzero : ∀ i ∈ v.support, J (generator i) ≠ 0)
    (hfree : ∀ j, (J v) j ≤ 1)
    (w : IntegralLattice ι) (hw : w.support ⊆ v.support)
    (himage : J w ∈ effective) : w ∈ effective := by
  classical
  intro i
  by_cases hiw : i ∈ w.support
  · have hi := hw hiw
    obtain ⟨j, hj, hother⟩ :=
      exists_isolating_coordinate J v hv hpositive hfree i hi (hnonzero i hi)
    have heq : (J w) j = w i := by
      rw [linear_apply_coefficient]
      rw [Finset.sum_eq_single i]
      · simp [hj]
      · intro k hk hki
        rw [hother k (hw hk) hki, mul_zero]
      · exact fun h => (h hiw).elim
    rw [← heq]
    exact himage j
  · simp [Finsupp.notMem_support_iff.mp hiw]

theorem positiveSupport : PositiveSupportStatement (ι := ι) (κ := κ) :=
  ⟨support_generator_image_subset_of_nonnegative_scalar,
    effective_of_effective_image_on_support⟩

end Langlands.VirtualRepresentation
