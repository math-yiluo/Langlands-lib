import Langlands.Group.RelativeWeylMinimalityProof

/-!
# The longest-survivor criterion for parabolic representatives

Exchange in a product shows that a right ascent leaving `D(J,∅)` conjugates
to a simple reflection in `J`; this gives the criterion for `longestRep`.
Conversely, the criterion makes the longest member of `W_J w` have every
simple reflection as a right descent. Such an element is unique, and left
length additivity then identifies `w` with `longestRep`.
-/

namespace Langlands.Group.RelativeWeylIndexing

universe u v
variable {B : Type u} {W : Type v} [Group W]
variable {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

open Classical
noncomputable section

theorem mem_positiveSimpleSet [Fintype B] (w : W) (i : B) :
    i ∈ positiveSimpleSet cs w ↔ cs.length w < cs.length (w * cs.simple i) := by
  simp [positiveSimpleSet]

/-- A left simple descent of a product is a left descent of the first factor,
or it is absorbed by a strictly shorter second factor. -/
theorem simple_left_exchange_mul {x y : W} {i : B}
    (hi : cs.length (cs.simple i * (x * y)) < cs.length (x * y)) :
    cs.length (cs.simple i * x) < cs.length x ∨
      ∃ y' : W, cs.simple i * (x * y) = x * y' ∧ cs.length y' < cs.length y := by
  obtain ⟨α, hα, rfl⟩ := cs.exists_isReduced x
  obtain ⟨β, hβ, rfl⟩ := cs.exists_isReduced y
  have hd : cs.length (cs.simple i * cs.wordProd (α ++ β)) <
      cs.length (cs.wordProd (α ++ β)) := by
    simpa [CoxeterSystem.wordProd_append] using hi
  rcases simple_left_exchange_append cs hd with ⟨k, hk, he⟩ | ⟨k, hk, he⟩
  · left
    have hs : cs.simple i * cs.wordProd α = cs.wordProd (α.eraseIdx k) := by
      apply mul_right_cancel (b := cs.wordProd β)
      simpa [CoxeterSystem.wordProd_append, mul_assoc] using he
    rw [hs, hα.eq]
    have hb := cs.length_wordProd_le (α.eraseIdx k)
    have hl := List.length_eraseIdx_add_one hk
    omega
  · right
    refine ⟨cs.wordProd (β.eraseIdx k), ?_, ?_⟩
    · simpa [CoxeterSystem.wordProd_append] using he
    · rw [hβ.eq]
      have hb := cs.length_wordProd_le (β.eraseIdx k)
      have hl := List.length_eraseIdx_add_one hk
      omega

/-- A form of Deodhar's lemma: if right multiplication of a left `J`-minimum
`w` by `s_i` creates the left descent `s_j`, `j ∈ J`, then
`w s_i w⁻¹ = s_j`. -/
theorem conj_simple_of_left_descent_mul_simple {J : Finset B} {w : W} {i j : B}
    (hw : ∀ j ∈ J, cs.length w < cs.length (cs.simple j * w)) (hj : j ∈ J)
    (hd : cs.length (cs.simple j * (w * cs.simple i)) <
      cs.length (w * cs.simple i)) :
    w * cs.simple i * w⁻¹ = cs.simple j := by
  rcases simple_left_exchange_mul cs hd with h | ⟨y, he, hy⟩
  · have := hw j hj
    omega
  · rw [cs.length_simple] at hy
    have hy1 : y = 1 := cs.length_eq_zero_iff.mp (by omega)
    subst hy1
    calc
      w * cs.simple i * w⁻¹ =
          cs.simple j * (w * cs.simple i) * cs.simple i * w⁻¹ := by
        rw [he, mul_one]
      _ = cs.simple j := by simp [mul_assoc]

/-- The constructed longest member of `D(J,∅)` sends every right ascent to a
simple reflection indexed by `J`. -/
theorem mapsIntoSimple_longestRep [Fintype B] [Fintype W] (J : Finset B) :
    MapsIntoSimple cs (longestRep cs J) (positiveSimpleSet cs (longestRep cs J)) J := by
  set w := longestRep cs J
  have hwmin : IsMinimal cs J ∅ w :=
    (mem_minimalReps cs J ∅ w).mp (longestRep_mem cs J)
  have hwL := ((minimalityLengthCriterion_proof cs J ∅ w).mp hwmin).1
  intro i hi
  have hi' := (mem_positiveSimpleSet cs w i).mp hi
  have hnot : ¬IsMinimal cs J ∅ (w * cs.simple i) := by
    intro h
    have : cs.length (w * cs.simple i) ≤ cs.length w :=
      length_le_longestRep cs J ((mem_minimalReps cs J ∅ _).mpr h)
    omega
  have hex : ∃ j ∈ J, ¬cs.length (w * cs.simple i) <
      cs.length (cs.simple j * (w * cs.simple i)) := by
    by_contra hall
    push Not at hall
    exact hnot ((minimalityLengthCriterion_proof cs J ∅ _).mpr ⟨hall, by simp⟩)
  obtain ⟨j, hj, hjn⟩ := hex
  have hd : cs.length (cs.simple j * (w * cs.simple i)) <
      cs.length (w * cs.simple i) := by
    have := cs.length_simple_mul_ne (w * cs.simple i) j
    omega
  exact ⟨j, hj, conj_simple_of_left_descent_mul_simple cs hwL hj hd⟩

/-- Under the survivor condition, a longest member of `W_J w` has every simple
reflection as a right descent. -/
theorem exists_full_descent_of_mapsIntoSimple [Fintype B] [Fintype W]
    {J : Finset B} {w : W}
    (hw : ∀ a ∈ standardSubgroup cs J, cs.length w ≤ cs.length (a * w))
    (hP : MapsIntoSimple cs w (positiveSimpleSet cs w) J) :
    ∃ a ∈ standardSubgroup cs J, ∀ i : B,
      cs.length (a * w * cs.simple i) < cs.length (a * w) := by
  let S : Finset W := Finset.univ.filter (fun a => a ∈ standardSubgroup cs J)
  have hS : S.Nonempty := ⟨1, by simp [S, (standardSubgroup cs J).one_mem]⟩
  obtain ⟨a, haS, hmax⟩ := S.exists_max_image (fun a => cs.length (a * w)) hS
  have ha : a ∈ standardSubgroup cs J := by simpa [S] using haS
  refine ⟨a, ha, fun i => ?_⟩
  have hne := cs.length_mul_simple_ne (a * w) i
  rcases cs.length_mul_simple w i with hup | hdown
  · obtain ⟨j, hj, hc⟩ := hP i ((mem_positiveSimpleSet cs w i).mpr (by omega))
    have hmem : a * cs.simple j ∈ standardSubgroup cs J :=
      (standardSubgroup cs J).mul_mem ha (simple_mem_standardSubgroup cs hj)
    have hle := hmax (a * cs.simple j) (by simpa [S] using hmem)
    have heq : a * cs.simple j * w = a * w * cs.simple i := by
      rw [← hc]
      group
    rw [heq] at hle
    omega
  · have hadd := length_mul_of_left_minimal cs hw ha
    have hle := cs.length_mul_le a (w * cs.simple i)
    rw [← mul_assoc] at hle
    omega

/-- An element with every simple reflection as a right descent has a
length-additive factorization ending in any prescribed element. -/
theorem exists_suffix_of_full_descent {u : W}
    (hu : ∀ i : B, cs.length (u * cs.simple i) < cs.length u) :
    ∀ (n : ℕ) (x : W), cs.length x = n →
      ∃ z : W, u = z * x ∧ cs.length u = cs.length z + cs.length x := by
  intro n
  induction n with
  | zero =>
    intro x hx
    refine ⟨u, ?_, ?_⟩ <;> simp [cs.length_eq_zero_iff.mp hx]
  | succ n ih =>
    intro x hx
    have hx1 : x ≠ 1 := by
      rintro rfl
      simp at hx
    obtain ⟨i, hi⟩ := cs.exists_rightDescent_of_ne_one hx1
    have hi' : cs.length (x * cs.simple i) + 1 = cs.length x :=
      cs.isRightDescent_iff.mp hi
    obtain ⟨z, hz, hl⟩ := ih (x * cs.simple i) (by omega)
    have hinv : u⁻¹ = (x * cs.simple i)⁻¹ * z⁻¹ := by
      rw [hz, mul_inv_rev]
    have hdesc : cs.length (cs.simple i * ((x * cs.simple i)⁻¹ * z⁻¹)) <
        cs.length ((x * cs.simple i)⁻¹ * z⁻¹) := by
      rw [← hinv, ← cs.length_inv (cs.simple i * u⁻¹), cs.length_inv u]
      simpa [mul_inv_rev] using hu i
    rcases simple_left_exchange_mul cs hdesc with h | ⟨y, he, hy⟩
    · have h1 : cs.simple i * (x * cs.simple i)⁻¹ = x⁻¹ := by
        simp [mul_inv_rev]
      rw [h1, cs.length_inv, cs.length_inv] at h
      omega
    · rw [← hinv] at he
      have hu' : u = y⁻¹ * x := by
        have h2 : u⁻¹ = x⁻¹ * y := by
          calc
            u⁻¹ = cs.simple i * (cs.simple i * u⁻¹) := by simp
            _ = cs.simple i * ((x * cs.simple i)⁻¹ * y) := by rw [he]
            _ = x⁻¹ * y := by simp [mul_inv_rev, ← mul_assoc]
        rw [← inv_inv u, h2, mul_inv_rev, inv_inv]
      refine ⟨y⁻¹, hu', ?_⟩
      have hb := cs.length_mul_le y⁻¹ x
      rw [← hu', cs.length_inv] at hb
      rw [cs.length_inv] at hy ⊢
      omega

/-- At most one element has every simple reflection as a right descent. -/
theorem eq_of_full_descent {u v : W}
    (hu : ∀ i : B, cs.length (u * cs.simple i) < cs.length u)
    (hv : ∀ i : B, cs.length (v * cs.simple i) < cs.length v) : u = v := by
  obtain ⟨z, hz, hl⟩ := exists_suffix_of_full_descent cs hu _ v rfl
  obtain ⟨z', -, hl'⟩ := exists_suffix_of_full_descent cs hv _ u rfl
  have h0 : cs.length z = 0 := by omega
  rw [hz, cs.length_eq_zero_iff.mp h0, one_mul]

/-- The exact published longest-survivor criterion. -/
theorem longestSurvivor_proof [Fintype B] [Fintype W] : longestSurvivor cs := by
  intro J w hw
  constructor
  · intro hP
    set v := longestRep cs J
    have hv : IsMinimal cs J ∅ v :=
      (mem_minimalReps cs J ∅ v).mp (longestRep_mem cs J)
    have hPv := mapsIntoSimple_longestRep cs J
    have hwL : ∀ a ∈ standardSubgroup cs J, cs.length w ≤ cs.length (a * w) := by
      intro a ha
      simpa using hw a ha 1 (standardSubgroup cs ∅).one_mem
    have hvL : ∀ a ∈ standardSubgroup cs J, cs.length v ≤ cs.length (a * v) := by
      intro a ha
      simpa using hv a ha 1 (standardSubgroup cs ∅).one_mem
    obtain ⟨a, ha, hfa⟩ := exists_full_descent_of_mapsIntoSimple cs hwL hP
    obtain ⟨b, hb, hfb⟩ := exists_full_descent_of_mapsIntoSimple cs hvL hPv
    have hab : a * w = b * v := eq_of_full_descent cs hfa hfb
    have hc : b⁻¹ * a ∈ standardSubgroup cs J :=
      (standardSubgroup cs J).mul_mem ((standardSubgroup cs J).inv_mem hb) ha
    have hvc : v = b⁻¹ * a * w := by
      rw [mul_assoc, hab, inv_mul_cancel_left]
    have h1 := length_mul_of_left_minimal cs hwL hc
    have h2 := length_mul_of_left_minimal cs hvL
      ((standardSubgroup cs J).inv_mem hc)
    have hw' : (b⁻¹ * a)⁻¹ * v = w := by
      rw [hvc, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [← hvc] at h1
    rw [hw', cs.length_inv] at h2
    have hc0 : cs.length (b⁻¹ * a) = 0 := by omega
    rw [hvc, cs.length_eq_zero_iff.mp hc0, one_mul]
  · rintro rfl
    exact mapsIntoSimple_longestRep cs J

end
end Langlands.Group.RelativeWeylIndexing
