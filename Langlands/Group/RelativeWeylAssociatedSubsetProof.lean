import Langlands.Group.RelativeWeylMinimalityProof
import Langlands.Group.CoxeterSimpleInjective

/-!
# The associated subset of the longest parabolic representative

A longest element of a finite standard subgroup has every simple reflection of
that subgroup as a left descent. Exchange then splits off any element of the
subgroup as a reduced prefix, so such a longest element conjugates each simple
reflection of the subgroup to a simple reflection. Writing the longest
representative as a product of two longest elements gives the three laws.
-/

namespace Langlands.Group.RelativeWeylIndexing

universe u v
variable {B : Type u} {W : Type v} [Group W]
variable {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

open Classical
noncomputable section

/-- Exchange reduces a standard word while keeping its letters in the same subset. -/
private theorem reduce_word_on {I : Finset B} (α : List B)
    (hα : ∀ i ∈ α, i ∈ I) :
    ∃ β : List B, (∀ i ∈ β, i ∈ I) ∧ cs.IsReduced β ∧
      cs.wordProd β = cs.wordProd α := by
  induction α with
  | nil => exact ⟨[], by simp, by simp [CoxeterSystem.IsReduced], rfl⟩
  | cons i α ih =>
    obtain ⟨β, hβ, hr, hp⟩ := ih (fun j hj => hα j (by simp [hj]))
    rcases cs.length_simple_mul (cs.wordProd β) i with hu | hd
    · refine ⟨i :: β, ?_, ?_, ?_⟩
      · simpa using And.intro (hα i (by simp)) hβ
      · change cs.length (cs.wordProd (i :: β)) = (i :: β).length
        rw [CoxeterSystem.wordProd_cons, hu, hr.eq, List.length_cons]
      · simp only [CoxeterSystem.wordProd_cons, hp]
    · have hdesc : cs.length (cs.simple i * cs.wordProd β) <
          cs.length (cs.wordProd β) := by omega
      obtain ⟨k, hk, he⟩ := simple_left_exchange cs hdesc
      refine ⟨β.eraseIdx k, fun j hj => hβ j (List.mem_of_mem_eraseIdx hj), ?_, ?_⟩
      · change cs.length (cs.wordProd (β.eraseIdx k)) = (β.eraseIdx k).length
        have hl := List.length_eraseIdx_add_one hk
        rw [← he]
        have hr' := hr.eq
        omega
      · rw [← he, CoxeterSystem.wordProd_cons, hp]

/-- Every standard-subgroup element has a reduced word on its own indices. -/
private theorem exists_reduced_word_on {I : Finset B} {a : W}
    (ha : a ∈ standardSubgroup cs I) :
    ∃ α : List B, (∀ i ∈ α, i ∈ I) ∧ cs.IsReduced α ∧ cs.wordProd α = a := by
  obtain ⟨β, hβ, hpβ⟩ := exists_standard_word cs ha
  obtain ⟨α, hα, hr, hpα⟩ := reduce_word_on cs β hβ
  exact ⟨α, hα, hr, hpα.trans hpβ⟩

/-- A reduced prefix of `a` stays a reduced prefix after a left letter that is a
descent of `a` and lengthens the prefix. -/
theorem length_prefix_step {a x : W} {i : B}
    (hx : cs.length (x⁻¹ * a) + cs.length x = cs.length a)
    (hi : cs.length (cs.simple i * a) < cs.length a)
    (hix : cs.length (cs.simple i * x) = cs.length x + 1) :
    cs.length ((cs.simple i * x)⁻¹ * a) + cs.length (cs.simple i * x) =
      cs.length a := by
  obtain ⟨α, hα, rfl⟩ := cs.exists_isReduced x
  obtain ⟨η, hη, hηp⟩ := cs.exists_isReduced ((cs.wordProd α)⁻¹ * a)
  have ha : a = cs.wordProd (α ++ η) := by
    rw [CoxeterSystem.wordProd_append, ← hηp, mul_inv_cancel_left]
  rw [ha] at hi
  rcases simple_left_exchange_append cs hi with ⟨k, hk, he⟩ | ⟨k, hk, he⟩
  · exfalso
    have hs : cs.simple i * cs.wordProd α = cs.wordProd (α.eraseIdx k) := by
      rw [CoxeterSystem.wordProd_append, CoxeterSystem.wordProd_append,
        ← mul_assoc] at he
      exact mul_right_cancel he
    have hle := cs.length_wordProd_le (α.eraseIdx k)
    have hl := List.length_eraseIdx_add_one hk
    rw [← hs, hix, hα.eq] at hle
    omega
  · have hs : (cs.simple i * cs.wordProd α)⁻¹ * a = cs.wordProd (η.eraseIdx k) := by
      rw [CoxeterSystem.wordProd_append, CoxeterSystem.wordProd_append] at he
      rw [mul_inv_rev, CoxeterSystem.inv_simple, ha, CoxeterSystem.wordProd_append,
        mul_assoc, he, inv_mul_cancel_left]
    have hle := cs.length_wordProd_le (η.eraseIdx k)
    have hl := List.length_eraseIdx_add_one hk
    have hge := cs.length_mul_le (cs.simple i * cs.wordProd α)
      ((cs.simple i * cs.wordProd α)⁻¹ * a)
    rw [mul_inv_cancel_left] at hge
    rw [← hs] at hle
    have hηl : cs.length ((cs.wordProd α)⁻¹ * a) = η.length := by rw [hηp, hη.eq]
    omega

/-- If every simple reflection of `I` is a left descent of `a`, then every
element of the standard subgroup `W_I` is a reduced prefix of `a`. -/
theorem length_inv_mul_add_of_descents {I : Finset B} {a : W}
    (ha : ∀ i ∈ I, cs.length (cs.simple i * a) < cs.length a) {x : W}
    (hx : x ∈ standardSubgroup cs I) :
    cs.length (x⁻¹ * a) + cs.length x = cs.length a := by
  obtain ⟨α, hαI, hα, rfl⟩ := exists_reduced_word_on cs hx
  clear hx
  induction α with
  | nil => simp
  | cons i α ih =>
    have hr : cs.IsReduced α := by simpa using hα.drop 1
    have hstep := ih (fun j hj => hαI j (List.mem_cons_of_mem i hj)) hr
    have hix : cs.length (cs.simple i * cs.wordProd α) =
        cs.length (cs.wordProd α) + 1 := by
      have h1 := hα.eq
      rw [CoxeterSystem.wordProd_cons] at h1
      rw [h1, hr.eq, List.length_cons]
    rw [CoxeterSystem.wordProd_cons]
    exact length_prefix_step cs hstep (ha i (hαI i (by simp))) hix

/-- A longest element of `W_I` conjugates each simple reflection of `I` to a
simple reflection. -/
theorem exists_simple_conj_of_longest {I : Finset B} {b : W}
    (hb : b ∈ standardSubgroup cs I)
    (hmax : ∀ y ∈ standardSubgroup cs I, cs.length y ≤ cs.length b)
    {i : B} (hi : i ∈ I) :
    ∃ k : B, b⁻¹ * cs.simple i * b = cs.simple k := by
  have hdesc : ∀ j ∈ I, cs.length (cs.simple j * b) < cs.length b := by
    intro j hj
    have hle := hmax _ ((standardSubgroup cs I).mul_mem
      (simple_mem_standardSubgroup cs hj) hb)
    rcases cs.length_simple_mul b j with h | h <;> omega
  have hx : cs.simple i * b ∈ standardSubgroup cs I :=
    (standardSubgroup cs I).mul_mem (simple_mem_standardSubgroup cs hi) hb
  have h := length_inv_mul_add_of_descents cs hdesc hx
  have hl := hdesc i hi
  have h1 : cs.length (b⁻¹ * cs.simple i * b) = 1 := by
    rw [mul_inv_rev, CoxeterSystem.inv_simple] at h
    rcases cs.length_simple_mul b i with h' | h' <;> omega
  obtain ⟨k, hk⟩ := cs.length_eq_one_iff.mp h1
  exact ⟨k, hk⟩

/-- Membership in the constructed simple image, with its filter unfolded. -/
private theorem mem_simpleImage [Fintype B] {w : W} {I : Finset B} {k : B} :
    k ∈ simpleImage cs w I ↔ ∃ i ∈ I, w * cs.simple i * w⁻¹ = cs.simple k := by
  unfold simpleImage
  simp

/-- The longest representative conjugates each simple reflection of `J` by
its inverse to a simple reflection. -/
private theorem longestRep_conj_simple [Fintype W] [Fintype B] (J : Finset B)
    {j : B} (hj : j ∈ J) :
    ∃ k : B, (longestRep cs J)⁻¹ * cs.simple j * longestRep cs J = cs.simple k := by
  set d := longestRep cs J with hd
  have hdmin : IsMinimal cs J ∅ d := (mem_minimalReps cs J ∅ d).mp (longestRep_mem cs J)
  have hdL : ∀ x ∈ standardSubgroup cs J, cs.length d ≤ cs.length (x * d) := by
    intro x hx
    simpa using hdmin x hx 1 (standardSubgroup cs ∅).one_mem
  obtain ⟨b, hbmem, hbmax⟩ := (Finset.univ.filter
    (fun y => y ∈ standardSubgroup cs J)).exists_max_image cs.length
    ⟨1, by simp⟩
  have hb : b ∈ standardSubgroup cs J := by simpa using hbmem
  have hbmax' : ∀ y ∈ standardSubgroup cs J, cs.length y ≤ cs.length b :=
    fun y hy => hbmax y (by simpa using hy)
  have hw : cs.length (b⁻¹ * d) = cs.length b + cs.length d := by
    rw [length_mul_of_left_minimal cs hdL ((standardSubgroup cs J).inv_mem hb),
      cs.length_inv]
  have hwmax : ∀ y ∈ standardSubgroup cs Finset.univ,
      cs.length y ≤ cs.length (b⁻¹ * d) := by
    intro y _
    obtain ⟨z, ⟨a, ha, c, hc, hz⟩, hzmin⟩ := exists_minimal_in_doubleCoset cs J ∅ y
    have hc1 : c = 1 := by simpa using hc
    subst hc1
    have hzL : ∀ x ∈ standardSubgroup cs J, cs.length z ≤ cs.length (x * z) := by
      intro x hx
      simpa using hzmin x hx 1 (standardSubgroup cs ∅).one_mem
    have hy : y = a⁻¹ * z := by rw [hz]; group
    have hly : cs.length y = cs.length a⁻¹ + cs.length z := by
      rw [hy]
      exact length_mul_of_left_minimal cs hzL ((standardSubgroup cs J).inv_mem ha)
    have h1 := hbmax' _ ((standardSubgroup cs J).inv_mem ha)
    have h2 : cs.length z ≤ cs.length d :=
      length_le_longestRep cs J ((mem_minimalReps cs J ∅ z).mpr hzmin)
    rw [hw]
    omega
  obtain ⟨m, hm⟩ := exists_simple_conj_of_longest cs hb hbmax' hj
  obtain ⟨k, hk⟩ := exists_simple_conj_of_longest cs
    (by rw [standardSubgroup_univ]; exact Subgroup.mem_top _) hwmax
    (Finset.mem_univ m)
  refine ⟨k, ?_⟩
  rw [← hk, ← hm]
  group

/-- The associated subset laws for the chosen longest representative. -/
theorem associatedSubsetLaws_proof [Fintype B] [Fintype W] :
    associatedSubsetLaws cs := by
  intro J
  set d := longestRep cs J with hd
  have hmaps : ∀ j ∈ J, ∃ k : B, d⁻¹ * cs.simple j * d⁻¹⁻¹ = cs.simple k := by
    intro j hj
    rw [inv_inv]
    exact longestRep_conj_simple cs J hj
  refine ⟨fun j hj => ?_, ?_, ?_⟩
  · obtain ⟨k, hk⟩ := hmaps j hj
    exact ⟨k, Finset.mem_univ k, hk⟩
  · symm
    refine Finset.card_bij (fun j hj => Classical.choose (hmaps j hj)) ?_ ?_ ?_
    · intro j hj
      exact (mem_simpleImage cs).mpr ⟨j, hj, Classical.choose_spec (hmaps j hj)⟩
    · intro j₁ hj₁ j₂ hj₂ he
      have h1 := Classical.choose_spec (hmaps j₁ hj₁)
      have h2 := Classical.choose_spec (hmaps j₂ hj₂)
      rw [← he, ← h1] at h2
      exact (simple_injective cs (mul_left_cancel (mul_right_cancel h2))).symm
    · intro k hk
      obtain ⟨j, hj, hjk⟩ := (mem_simpleImage cs).mp hk
      refine ⟨j, hj, simple_injective cs ?_⟩
      rw [← Classical.choose_spec (hmaps j hj), hjk]
  · rw [associatedSubset, conjugateStandardSubgroup, standardSubgroup, standardSubgroup,
      MonoidHom.map_closure]
    congr 1
    ext x
    simp only [Set.mem_image, Finset.mem_coe, mem_simpleImage]
    constructor
    · rintro ⟨k, ⟨j, hj, hjk⟩, rfl⟩
      exact ⟨cs.simple j, ⟨j, hj, rfl⟩, by simpa [MulAut.conj_apply] using hjk⟩
    · rintro ⟨y, ⟨j, hj, rfl⟩, rfl⟩
      obtain ⟨k, hk⟩ := hmaps j hj
      exact ⟨k, ⟨j, hj, hk⟩, by simpa [MulAut.conj_apply] using hk.symm⟩

end

end Langlands.Group.RelativeWeylIndexing
