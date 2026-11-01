import Langlands.VirtualRepresentation.Integral
import Mathlib.Data.Finsupp.Order

/-! Positive integral images of the constituents of a fixed effective vector. -/

noncomputable section

namespace Langlands.VirtualRepresentation

open scoped BigOperators

universe u

variable {ι : Type u}

/-- The sum of integral multiplicities; on an effective vector it counts
constituents with multiplicity. -/
def multiplicitySum : IntegralLattice ι →ₗ[ℤ] ℤ :=
  extend (fun _ => 1)

theorem multiplicitySum_apply (v : IntegralLattice ι) :
    multiplicitySum v = ∑ i ∈ v.support, v i := by
  simp [multiplicitySum, extend, Finsupp.linearCombination_apply, Finsupp.sum]

@[simp] theorem multiplicitySum_generator (i : ι) :
    multiplicitySum (generator i) = 1 := by
  simp [multiplicitySum, extend, generator]

/-- Every nonzero effective integral combination has positive total
multiplicity. -/
theorem multiplicitySum_pos {v : IntegralLattice ι}
    (hv : v ∈ effective) (hne : v ≠ 0) : 0 < multiplicitySum v := by
  rw [multiplicitySum_apply]
  apply Finset.sum_pos
  · intro i hi
    have hnonneg : 0 ≤ v i := hv i
    have hne' : v i ≠ 0 := Finsupp.mem_support_iff.mp hi
    omega
  · exact Finsupp.support_nonempty_iff.mpr hne

/-- An effective integral vector of total multiplicity one is a genuine
basis generator. -/
theorem eq_generator_of_effective_of_multiplicitySum_eq_one
    {v : IntegralLattice ι} (hv : v ∈ effective)
    (h : multiplicitySum v = 1) : ∃ i, v = generator i := by
  classical
  have hne : v ≠ 0 := by
    intro hz
    simp [hz] at h
  obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hne
  have hpos : 0 < v i := by
    have hnonneg : 0 ≤ v i := hv i
    have hne' := Finsupp.mem_support_iff.mp hi
    omega
  have hle : v i ≤ multiplicitySum v := by
    rw [multiplicitySum_apply]
    exact Finset.single_le_sum (fun j _ => hv j) hi
  have hvi : v i = 1 := by omega
  have hrest : ∑ j ∈ v.support.erase i, v j = 0 := by
    have heq := Finset.sum_erase_add v.support (fun j => v j) hi
    rw [← multiplicitySum_apply, h, hvi] at heq
    omega
  have hzero : ∀ j ∈ v.support.erase i, v j = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hv j)).mp hrest
  refine ⟨i, Finsupp.ext fun j => ?_⟩
  by_cases hji : j = i
  · subst j
    simp [generator, hvi]
  · by_cases hj : j ∈ v.support
    · simpa [generator, hji] using hzero j (Finset.mem_erase.mpr ⟨hji, hj⟩)
    · simp [generator, hji, Finsupp.notMem_support_iff.mp hj]

/-- Let an injective integral linear map fix an effective vector. If the
images of all basis constituents of that vector are effective, then each of
those images is a basis generator. This is the finite-length counting step:
nonzero effective columns have total multiplicity at least one, and their
positive weighted sum has unchanged total multiplicity. -/
theorem generator_image_of_effective_fixed
    (L : IntegralLattice ι →ₗ[ℤ] IntegralLattice ι)
    (hL : Function.Injective L) (v : IntegralLattice ι)
    (hv : v ∈ effective) (hfix : L v = v)
    (hpositive : ∀ i ∈ v.support, L (generator i) ∈ effective) :
    ∀ i ∈ v.support, ∃ j, L (generator i) = generator j := by
  classical
  have hcol (i : ι) : L (generator i) ≠ 0 := by
    intro h
    have hz : generator i = (0 : IntegralLattice ι) := hL (h.trans (map_zero L).symm)
    have hi := DFunLike.congr_fun hz i
    simp [generator] at hi
  have hmass (i : ι) (hi : i ∈ v.support) :
      1 ≤ multiplicitySum (L (generator i)) := by
    have hp := multiplicitySum_pos (hpositive i hi) (hcol i)
    omega
  have hexpand : v = ∑ i ∈ v.support, v i • generator i := by
    conv_lhs => rw [← Finsupp.sum_single v]
    apply Finset.sum_congr rfl
    intro i _
    simp [generator]
  have htotal :
      (∑ i ∈ v.support, v i * multiplicitySum (L (generator i))) =
        ∑ i ∈ v.support, v i := by
    have heq := congrArg multiplicitySum hfix
    conv_rhs at heq => rw [multiplicitySum_apply]
    conv_lhs at heq => rw [hexpand, map_sum, map_sum]
    simpa only [map_zsmul, zsmul_eq_mul, Int.cast_id] using heq
  have hterm (i : ι) (hi : i ∈ v.support) :
      v i ≤ v i * multiplicitySum (L (generator i)) := by
    exact le_mul_of_one_le_right (hv i) (hmass i hi)
  have heach := (Finset.sum_eq_sum_iff_of_le hterm).mp htotal.symm
  intro i hi
  apply eq_generator_of_effective_of_multiplicitySum_eq_one (hpositive i hi)
  have hcoeff : 0 < v i := by
    have hnonneg : 0 ≤ v i := hv i
    have hne := Finsupp.mem_support_iff.mp hi
    omega
  have heq := heach i hi
  apply mul_left_cancel₀ (ne_of_gt hcoeff)
  simpa only [mul_one] using heq.symm

end Langlands.VirtualRepresentation
