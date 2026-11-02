import Langlands.Group.RelativeWeylLongestSurvivorProof
import Langlands.Group.RelativeWeylSimpleInjective
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

namespace Langlands.Group.RelativeWeylIndexing

universe u v
variable {B : Type u} {W : Type v} [Group W]
variable {M : CoxeterMatrix B} (cs : CoxeterSystem M W) (hsi : Function.Injective cs.simple)

open Classical
open scoped BigOperators
noncomputable section

include hsi in
private theorem conjugate_simple_injective (w : W) {i j : B}
    (h : w * cs.simple i * w⁻¹ = w * cs.simple j * w⁻¹) : i = j := by
  apply hsi
  exact mul_left_cancel (mul_right_cancel h)

private theorem mem_simpleImage [Fintype B] (w : W) (I : Finset B) (j : B) :
    j ∈ simpleImage cs w I ↔ ∃ i ∈ I, w * cs.simple i * w⁻¹ = cs.simple j := by
  simp [simpleImage]

private theorem simpleImage_insert_bad [Fintype B] (w : W) (J I : Finset B)
    (i : B) (hi : ¬ ∃ j ∈ J, w * cs.simple i * w⁻¹ = cs.simple j) :
    simpleImage cs w (insert i I) ∩ J = simpleImage cs w I ∩ J := by
  ext j
  simp only [Finset.mem_inter, mem_simpleImage, Finset.mem_insert]
  constructor
  · rintro ⟨⟨k, hk, he⟩, hj⟩
    rcases hk with rfl | hk
    · exact (hi ⟨j, hj, he⟩).elim
    · exact ⟨⟨k, hk, he⟩, hj⟩
  · rintro ⟨⟨k, hk, he⟩, hj⟩
    exact ⟨⟨k, Or.inr hk, he⟩, hj⟩

/-- A domain index with no simple image in J pairs every term with its negative. -/
theorem jacquet_sum_zero_of_not_maps [Fintype B] (w : W) (P J K : Finset B)
    (h : ¬ MapsIntoSimple cs w P J) :
    (∑ I ∈ P.powerset,
      if simpleImage cs w I ∩ J = K then (-1 : ℤ) ^ I.card else 0) = 0 := by
  simp only [MapsIntoSimple, not_forall, not_exists, not_and] at h
  obtain ⟨i, hi, hbad⟩ := h
  rw [← Finset.insert_erase hi, Finset.sum_powerset_insert (Finset.notMem_erase i P)]
  have he : (∑ I ∈ (P.erase i).powerset,
      if simpleImage cs w (insert i I) ∩ J = K then (-1 : ℤ) ^ (insert i I).card
      else 0) =
      -(∑ I ∈ (P.erase i).powerset,
      if simpleImage cs w I ∩ J = K then (-1 : ℤ) ^ I.card else 0) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro I hI
    have hn : i ∉ I := fun hm =>
      (Finset.notMem_erase i P) ((Finset.mem_powerset.mp hI) hm)
    rw [simpleImage_insert_bad cs w J I i (by simpa using hbad), Finset.card_insert_of_notMem hn,
      pow_succ]
    split_ifs <;> ring
  rw [he]
  exact add_neg_cancel _

include hsi in
/-- If every domain label maps into J and its image covers J, every K has one preimage. -/
theorem jacquet_sum_of_maps_and_coverage [Fintype B] (w : W) (P J K : Finset B)
    (hm : MapsIntoSimple cs w P J) (hc : simpleImage cs w P = J) (hK : K ⊆ J) :
    (∑ I ∈ P.powerset,
      if simpleImage cs w I ∩ J = K then (-1 : ℤ) ^ I.card else 0) =
      (-1 : ℤ) ^ K.card := by
  let Q := P.filter (fun i => ∃ j ∈ K, w * cs.simple i * w⁻¹ = cs.simple j)
  have hQP : Q ⊆ P := Finset.filter_subset _ _
  have hQ : simpleImage cs w Q = K := by
    ext j
    rw [mem_simpleImage]
    constructor
    · rintro ⟨i, hi, he⟩
      obtain ⟨k, hk, hk'⟩ := (Finset.mem_filter.mp hi).2
      have hjk : j = k := hsi (he.symm.trans hk')
      simpa [hjk] using hk
    · intro hj
      obtain ⟨i, hi, he⟩ := (mem_simpleImage cs w P j).mp (hc.symm ▸ hK hj)
      exact ⟨i, Finset.mem_filter.mpr ⟨hi, ⟨j, hj, he⟩⟩, he⟩
  have hImage : ∀ I ⊆ P, simpleImage cs w I ⊆ J := by
    intro I hI j hj
    obtain ⟨i, hi, he⟩ := (mem_simpleImage cs w I j).mp hj
    obtain ⟨k, hk, hk'⟩ := hm i (hI hi)
    have hjk : j = k := hsi (he.symm.trans hk')
    simpa [hjk] using hk
  have hUnique : ∀ I ⊆ P, simpleImage cs w I ∩ J = K ↔ I = Q := by
    intro I hI
    rw [Finset.inter_eq_left.mpr (hImage I hI)]
    constructor
    · intro he
      apply Finset.Subset.antisymm
      · intro i hi
        obtain ⟨j, hj, hij⟩ := hm i (hI hi)
        have hj' : j ∈ K := he ▸ (mem_simpleImage cs w I j).mpr ⟨i, hi, hij⟩
        exact Finset.mem_filter.mpr ⟨hI hi, j, hj', hij⟩
      · intro i hi
        obtain ⟨j, hj, hij⟩ := (Finset.mem_filter.mp hi).2
        obtain ⟨k, hk, hkj⟩ := (mem_simpleImage cs w I j).mp (he.symm ▸ hj)
        have hik : i = k := conjugate_simple_injective cs hsi w (hij.trans hkj.symm)
        simpa [hik] using hk
    · rintro rfl
      exact hQ
  have hcard : Q.card = K.card := by
    apply Finset.card_bij
      (fun i hi => Classical.choose (hm i (hQP hi)))
    · intro i hi
      have hp := Classical.choose_spec (hm i (hQP hi))
      rw [← hQ]
      exact (mem_simpleImage cs w Q _).mpr ⟨i, hi, hp.2⟩
    · intro i hi k hk he
      exact conjugate_simple_injective cs hsi w
        ((Classical.choose_spec (hm i (hQP hi))).2.trans
          ((congrArg cs.simple he).trans
            (Classical.choose_spec (hm k (hQP hk))).2.symm))
    · intro j hj
      obtain ⟨i, hi, he⟩ := (mem_simpleImage cs w Q j).mp (hQ.symm ▸ hj)
      refine ⟨i, hi, ?_⟩
      exact hsi
        ((Classical.choose_spec (hm i (hQP hi))).2.symm.trans he)
  calc
    _ = ∑ I ∈ P.powerset, if I = Q then (-1 : ℤ) ^ I.card else 0 := by
      apply Finset.sum_congr rfl
      intro I hI
      simp only [hUnique I (Finset.mem_powerset.mp hI)]
    _ = (-1 : ℤ) ^ Q.card := by simp [Finset.mem_powerset.mpr hQP]
    _ = _ := by rw [hcard]


/-- Under the survivor condition, every `j ∈ J` is the image of some positive
simple index: `s_j = w s_i w⁻¹` with `ℓ(w) < ℓ(w s_i)`. -/
theorem subset_simpleImage_of_mapsIntoSimple [Fintype B] [Fintype W]
    {J : Finset B} {w : W} (hw : IsMinimal cs J ∅ w)
    (hP : MapsIntoSimple cs w (positiveSimpleSet cs w) J) :
    J ⊆ simpleImage cs w (positiveSimpleSet cs w) := by
  have hwS := ((minimalityLengthCriterion_proof cs J ∅ w).mp hw).1
  have hwL : ∀ a ∈ standardSubgroup cs J, cs.length w ≤ cs.length (a * w) :=
    left_minimal_of_simple cs hwS
  obtain ⟨a, ha, hfull⟩ := exists_full_descent_of_mapsIntoSimple cs hwL hP
  intro j hj
  set r : W := w⁻¹ * cs.simple j * w with hr
  obtain ⟨z, hz, hlen⟩ := exists_suffix_of_full_descent cs hfull _ r rfl
  have hzeq : z = a * cs.simple j * w := by
    have h : z = a * w * r⁻¹ := by rw [hz, mul_inv_cancel_right]
    rw [h, hr, mul_inv_rev, mul_inv_rev, inv_inv, CoxeterSystem.inv_simple]
    group
  have haj : a * cs.simple j ∈ standardSubgroup cs J :=
    (standardSubgroup cs J).mul_mem ha (simple_mem_standardSubgroup cs hj)
  have h1 := length_mul_of_left_minimal cs hwL ha
  have h2 := length_mul_of_left_minimal cs hwL haj
  have h3 : cs.length a ≤ cs.length (a * cs.simple j) + 1 := by
    have := cs.length_mul_le (a * cs.simple j) (cs.simple j)
    rwa [CoxeterSystem.simple_mul_simple_cancel_right, cs.length_simple] at this
  rw [hzeq] at hlen
  have hr0 : r ≠ 1 := by
    intro h
    have : cs.simple j = 1 := by
      calc
        cs.simple j = w * r * w⁻¹ := by rw [hr]; group
        _ = 1 := by rw [h]; group
    simpa [this] using cs.length_simple j
  have hr1 : cs.length r = 1 := by
    have : cs.length r ≠ 0 := fun h => hr0 (cs.length_eq_zero_iff.mp h)
    omega
  obtain ⟨i, hi⟩ := cs.length_eq_one_iff.mp hr1
  have hconj : w * cs.simple i * w⁻¹ = cs.simple j := by
    rw [← hi, hr]
    group
  have hpos : i ∈ positiveSimpleSet cs w := by
    rw [mem_positiveSimpleSet]
    have : w * cs.simple i = cs.simple j * w := by
      rw [← hconj]
      group
    rw [this]
    exact hwS j hj
  simp only [simpleImage, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨i, hpos, hconj⟩


/-- The exact pointwise coefficient identity, including intrinsic image coverage. -/
theorem jacquetCancellation_proof [Fintype B] [Fintype W] :
    jacquetCancellation cs := by
  intro J w hw K hK
  by_cases hm : MapsIntoSimple cs w (positiveSimpleSet cs w) J
  · simp only [hm, ↓reduceIte]
    have hc : simpleImage cs w (positiveSimpleSet cs w) = J := by
      apply Finset.Subset.antisymm
      · intro j hj
        obtain ⟨i, hi, he⟩ := (mem_simpleImage cs w _ j).mp hj
        obtain ⟨k, hk, he'⟩ := hm i hi
        have hjk : j = k := simple_reflection_injective cs (he.symm.trans he')
        simpa [hjk] using hk
      · exact subset_simpleImage_of_mapsIntoSimple cs hw hm
    exact jacquet_sum_of_maps_and_coverage cs (simple_reflection_injective cs)
      w (positiveSimpleSet cs w) J K hm hc hK
  · simp only [hm, ↓reduceIte]
    exact jacquet_sum_zero_of_not_maps cs w (positiveSimpleSet cs w) J K hm

end
end Langlands.Group.RelativeWeylIndexing
