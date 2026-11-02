import Langlands.Group.RelativeWeylMinimalityProof

/-!
# The longest minimal parabolic representative

A signed action of the Coxeter group records the parity of each reflection in
the left inversion sequence of any word. Its cocycle law gives the strong
exchange criterion for left multiplication by a reflection. At an element of
maximum length every reflection is then an inversion, which yields the length
complement `ℓ (x * w₀) + ℓ x = ℓ w₀`. The longest members of `D(J,∅)` are
therefore all equal to `a⁻¹ * w₀`, for a longest element `a` of `W_J`.
-/

namespace Langlands.Group.RelativeWeylIndexing

universe u v
variable {B : Type u} {W : Type v} [Group W]
variable {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

open Classical
noncomputable section

/-- The parity of the number of occurrences of `t` in the left inversion
sequence of any word for `w`; see `reflectionParity_wordProd`. -/
def reflectionParity (w t : W) : ZMod 2 :=
  signedAction cs w (fun _ => 0) t

/-- The parity is computed by the left inversion sequence of every word. -/
theorem reflectionParity_wordProd (ω : List B) (t : W) :
    reflectionParity cs (cs.wordProd ω) t = ((cs.leftInvSeq ω).count t : ZMod 2) := by
  simp [reflectionParity, signedAction_word, signedWord_apply]

private theorem parityAction_apply (w : W) (f : W → ZMod 2) (t : W) :
    signedAction cs w f t = f (w⁻¹ * t * w) + reflectionParity cs w t := by
  obtain ⟨ω, rfl⟩ := cs.wordProd_surjective w
  rw [reflectionParity_wordProd, signedAction_word, signedWord_apply]

/-- The parity function is a cocycle for the conjugation action. -/
theorem reflectionParity_mul (x y t : W) :
    reflectionParity cs (x * y) t =
      reflectionParity cs x t + reflectionParity cs y (x⁻¹ * t * x) := by
  change signedAction cs (x * y) (fun _ => 0) t = _
  rw [map_mul]
  change signedAction cs x (signedAction cs y (fun _ => 0)) t = _
  rw [parityAction_apply, add_comm]
  rfl

@[simp]
theorem reflectionParity_one (t : W) : reflectionParity cs 1 t = 0 := by
  simpa using reflectionParity_wordProd cs [] t

theorem reflectionParity_simple_self (i : B) :
    reflectionParity cs (cs.simple i) (cs.simple i) = 1 := by
  simpa [CoxeterSystem.leftInvSeq] using reflectionParity_wordProd cs [i] (cs.simple i)

/-- Every reflection occurs an odd number of times in its own inversion sequence. -/
theorem reflectionParity_self {t : W} (ht : cs.IsReflection t) :
    reflectionParity cs t t = 1 := by
  obtain ⟨w, i, rfl⟩ := ht
  have hconj : w⁻¹ * (w * cs.simple i * w⁻¹) * w = cs.simple i := by
    simp [mul_assoc]
  -- Conjugating back and forth contributes nothing in total.
  have hc := reflectionParity_mul cs w w⁻¹ (w * cs.simple i * w⁻¹)
  rw [mul_inv_cancel, reflectionParity_one, hconj] at hc
  have h1 := reflectionParity_mul cs w (cs.simple i * w⁻¹) (w * cs.simple i * w⁻¹)
  rw [show w * (cs.simple i * w⁻¹) = w * cs.simple i * w⁻¹ from (mul_assoc _ _ _).symm,
    hconj] at h1
  have h2 := reflectionParity_mul cs (cs.simple i) w⁻¹ (cs.simple i)
  rw [show (cs.simple i)⁻¹ * cs.simple i * cs.simple i = cs.simple i by simp] at h2
  rw [h1, h2, reflectionParity_simple_self, add_left_comm, ← hc, add_zero]

private theorem zmod_two_cases (x : ZMod 2) : x = 0 ∨ x = 1 := by
  revert x
  decide

/-- An odd inversion parity forces a strict length decrease. -/
theorem length_mul_lt_of_reflectionParity {w t : W}
    (h : reflectionParity cs w t = 1) : cs.length (t * w) < cs.length w := by
  obtain ⟨ω, hω, rfl⟩ := cs.exists_isReduced w
  rw [reflectionParity_wordProd] at h
  have hm : t ∈ cs.leftInvSeq ω := by
    by_contra hn
    rw [List.count_eq_zero_of_not_mem hn, Nat.cast_zero] at h
    exact zero_ne_one h
  exact (cs.isLeftInversion_of_mem_leftInvSeq hω hm).2

/-- The strong exchange criterion for left multiplication by a reflection. -/
theorem length_reflection_mul_lt_iff {w t : W} (ht : cs.IsReflection t) :
    cs.length (t * w) < cs.length w ↔ reflectionParity cs w t = 1 := by
  refine ⟨fun hlt => ?_, length_mul_lt_of_reflectionParity cs⟩
  rcases zmod_two_cases (reflectionParity cs w t) with h0 | h1
  · have he := reflectionParity_mul cs t w t
    rw [reflectionParity_self cs ht, show t⁻¹ * t * t = t by simp, h0, add_zero] at he
    have hgt := length_mul_lt_of_reflectionParity cs he
    rw [← mul_assoc, ht.mul_self, one_mul] at hgt
    omega
  · exact h1

/-- At an element of maximum length, length is complementary under left
multiplication. No finiteness of `W` is needed once such an element is given. -/
theorem length_mul_add_length_of_forall_length_le {w₀ : W}
    (hw₀ : ∀ x : W, cs.length x ≤ cs.length w₀) (x : W) :
    cs.length (x * w₀) + cs.length x = cs.length w₀ := by
  have hinv : ∀ t : W, cs.IsReflection t → reflectionParity cs w₀ t = 1 := by
    intro t ht
    have hle := hw₀ (t * w₀)
    have hne := ht.length_mul_right_ne w₀
    exact (length_reflection_mul_lt_iff cs ht).mp (by omega)
  induction hn : cs.length x generalizing x with
  | zero =>
    rw [cs.length_eq_zero_iff.mp hn]
    simp
  | succ n ih =>
    have hx : x ≠ 1 := by
      rintro rfl
      simp at hn
    obtain ⟨i, hi⟩ := cs.exists_leftDescent_of_ne_one hx
    let y := cs.simple i * x
    have hxy : x = cs.simple i * y := by
      simp [y]
    have hdesc : cs.length y < cs.length x := hi
    have hy : cs.length y = n := by
      rcases cs.length_simple_mul x i with h | h <;> simp only [y] at hdesc ⊢ <;> omega
    have ihy := ih y hy
    -- The simple reflection is not an inversion of `y`, but its conjugate is one of `w₀`.
    have hy0 : reflectionParity cs y (cs.simple i) = 0 := by
      rcases zmod_two_cases (reflectionParity cs y (cs.simple i)) with h | h
      · exact h
      · have hlt := length_mul_lt_of_reflectionParity cs h
        rw [← hxy] at hlt
        omega
    have hr : cs.IsReflection (y⁻¹ * cs.simple i * y) := by
      simpa using (cs.isReflection_simple i).conj y⁻¹
    have hp : reflectionParity cs (y * w₀) (cs.simple i) = 1 := by
      rw [reflectionParity_mul, hy0, hinv _ hr, zero_add]
    have hlt := length_mul_lt_of_reflectionParity cs hp
    rw [← mul_assoc, ← hxy] at hlt
    have hstep := cs.length_simple_mul (y * w₀) i
    rw [← mul_assoc, ← hxy] at hstep
    omega

/-- A finite Coxeter group has an element with complementary lengths. -/
theorem exists_length_complement [Fintype W] :
    ∃ w₀ : W, ∀ x : W, cs.length (x * w₀) + cs.length x = cs.length w₀ := by
  obtain ⟨w₀, -, hw₀⟩ := Finset.univ.exists_max_image cs.length Finset.univ_nonempty
  exact ⟨w₀, length_mul_add_length_of_forall_length_le cs
    (fun x => hw₀ x (Finset.mem_univ x))⟩

/-- An element of maximum length is unique. -/
theorem eq_of_forall_length_le {w₀ y : W}
    (hw₀ : ∀ x : W, cs.length x ≤ cs.length w₀) (hy : cs.length w₀ ≤ cs.length y) :
    y = w₀ := by
  have h := length_mul_add_length_of_forall_length_le cs hw₀ (y * w₀⁻¹)
  rw [inv_mul_cancel_right] at h
  have h1 : y * w₀⁻¹ = 1 := cs.length_eq_zero_iff.mp (by omega)
  exact mul_inv_eq_one.mp h1

/-- An element with every simple reflection as a right descent has maximum length. -/
theorem eq_of_forall_length_mul_simple_lt {w₀ c : W}
    (hw₀ : ∀ x : W, cs.length x ≤ cs.length w₀)
    (hc : ∀ i : B, cs.length (c * cs.simple i) < cs.length c) : c = w₀ := by
  have h := length_mul_add_length_of_forall_length_le cs hw₀ c⁻¹
  rw [cs.length_inv] at h
  by_cases hy : c⁻¹ * w₀ = 1
  · exact (inv_mul_eq_one.mp hy)
  · exfalso
    obtain ⟨i, hi⟩ := cs.exists_leftDescent_of_ne_one hy
    have hi' : cs.length (cs.simple i * (c⁻¹ * w₀)) < cs.length (c⁻¹ * w₀) := hi
    have hci := hc i
    have hsplit : w₀ = (c * cs.simple i) * (cs.simple i * (c⁻¹ * w₀)) := by
      simp [mul_assoc]
    have hle := cs.length_mul_le (c * cs.simple i) (cs.simple i * (c⁻¹ * w₀))
    rw [← hsplit] at hle
    rcases cs.length_mul_simple c i with h1 | h1 <;>
      rcases cs.length_simple_mul (c⁻¹ * w₀) i with h2 | h2 <;> omega

/-- Every longest member of `D(J,∅)` is `a⁻¹ * w₀`, for longest `a ∈ W_J` and `w₀ ∈ W`. -/
private theorem eq_inv_mul_of_longest_minimal [Fintype W] {J : Finset B} {w₀ a d : W}
    (hw₀ : ∀ x : W, cs.length x ≤ cs.length w₀)
    (ha : a ∈ standardSubgroup cs J)
    (haJ : ∀ b ∈ standardSubgroup cs J, cs.length b ≤ cs.length a)
    (hd : d ∈ minimalReps cs J ∅)
    (hmax : ∀ x ∈ minimalReps cs J ∅, cs.length x ≤ cs.length d) :
    d = a⁻¹ * w₀ := by
  have hcomp := length_mul_add_length_of_forall_length_le cs hw₀
  -- The candidate `a⁻¹ * w₀` is itself a minimal representative.
  have hmin : IsMinimal cs J ∅ (a⁻¹ * w₀) := by
    intro b hb c hc
    have hc1 : c = 1 := by simpa using hc
    subst c
    have h1 := hcomp a⁻¹
    have h2 := hcomp (b * a⁻¹)
    have h3 := haJ (b * a⁻¹)
      ((standardSubgroup cs J).mul_mem hb ((standardSubgroup cs J).inv_mem ha))
    rw [cs.length_inv] at h1
    rw [mul_one, ← mul_assoc]
    omega
  have hle := hmax _ ((mem_minimalReps cs J ∅ _).mpr hmin)
  have hdL : ∀ x ∈ standardSubgroup cs J, cs.length d ≤ cs.length (x * d) := by
    intro x hx
    simpa using (mem_minimalReps cs J ∅ d).mp hd x hx 1 (standardSubgroup cs ∅).one_mem
  have hadd := length_mul_of_left_minimal cs hdL ha
  have h1 := hcomp a⁻¹
  have h2 := hcomp (a * d * w₀⁻¹)
  rw [cs.length_inv] at h1
  rw [inv_mul_cancel_right, hadd] at h2
  have h3 : a * d * w₀⁻¹ = 1 := cs.length_eq_zero_iff.mp (by omega)
  have h4 : a * d = w₀ := mul_inv_eq_one.mp h3
  rw [← h4, inv_mul_cancel_left]

/-- The exact published uniqueness proposition for the longest member of `D(J,∅)`. -/
theorem longestRepresentativeUnique_proof [Fintype W] : longestRepresentativeUnique cs := by
  intro J w hw hmax
  obtain ⟨w₀, -, hw₀⟩ := Finset.univ.exists_max_image cs.length Finset.univ_nonempty
  have hw₀' : ∀ x : W, cs.length x ≤ cs.length w₀ := fun x => hw₀ x (Finset.mem_univ x)
  obtain ⟨a, ha, haJ⟩ := (Finset.univ.filter (· ∈ standardSubgroup cs J)).exists_max_image
    cs.length ⟨1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (standardSubgroup cs J).one_mem⟩⟩
  have ha' : a ∈ standardSubgroup cs J := (Finset.mem_filter.mp ha).2
  have haJ' : ∀ b ∈ standardSubgroup cs J, cs.length b ≤ cs.length a :=
    fun b hb => haJ b (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩)
  rw [eq_inv_mul_of_longest_minimal cs hw₀' ha' haJ' hw hmax,
    eq_inv_mul_of_longest_minimal cs hw₀' ha' haJ' (longestRep_mem cs J)
      (fun x hx => length_le_longestRep cs J hx)]

end
end Langlands.Group.RelativeWeylIndexing
