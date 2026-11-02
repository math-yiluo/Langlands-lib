import Langlands.Group.RelativeWeylMinimalityProof

/-!
# Uniqueness of Coxeter parabolic double-coset minima

Reduce a standard-subgroup word by exchange. An exchange induction then
identifies two minima in the same double coset.
-/

namespace Langlands.Group.RelativeWeylIndexing

universe u v
variable {B : Type u} {W : Type v} [Group W]
variable {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

open Classical
noncomputable section

/-- Exchange reduces a standard word while keeping its letters in the same subset. -/
private theorem reduce_standard_word {I : Finset B} (α : List B)
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

/-- Every standard-subgroup element has an ambient reduced word on its own indices. -/
private theorem reduced_standard_word_exists {I : Finset B} {a : W}
    (ha : a ∈ standardSubgroup cs I) :
    ∃ α : List B, (∀ i ∈ α, i ∈ I) ∧ cs.IsReduced α ∧ cs.wordProd α = a := by
  obtain ⟨β, hβ, hpβ⟩ := exists_standard_word cs ha
  obtain ⟨α, hα, hr, hpα⟩ := reduce_standard_word cs β hβ
  exact ⟨α, hα, hr, hpα.trans hpβ⟩

/-- Exchange removes the left word connecting two equal-length minima. -/
private theorem eq_of_minimal_word_relation {I J : Finset B} {x y : W}
    (hx : IsMinimal cs I J x) (hy : IsMinimal cs I J y)
    (hlen : cs.length x = cs.length y)
    (α : List B) (hα : ∀ i ∈ α, i ∈ I) (hr : cs.IsReduced α)
    (β : List B) (hβ : ∀ j ∈ β, j ∈ J)
    (he : cs.wordProd α * x = y * cs.wordProd β) : x = y := by
  have hxL : ∀ a ∈ standardSubgroup cs I, cs.length x ≤ cs.length (a * x) := by
    intro a ha
    simpa using hx a ha 1 (standardSubgroup cs J).one_mem
  have hyL : ∀ a ∈ standardSubgroup cs I, cs.length y ≤ cs.length (a * y) := by
    intro a ha
    simpa using hy a ha 1 (standardSubgroup cs J).one_mem
  have hyR : ∀ b ∈ standardSubgroup cs J, cs.length y ≤ cs.length (y * b) := by
    intro b hb
    simpa using hy 1 (standardSubgroup cs I).one_mem b hb
  induction α generalizing β with
  | nil =>
    have he' : x = y * cs.wordProd β := by simpa using he
    have hl := length_mul_of_right_minimal cs hyR (wordProd_mem_standard cs hβ)
    have hz : cs.length (cs.wordProd β) = 0 := by
      rw [← he', hlen] at hl
      omega
    have hp := cs.length_eq_zero_iff.mp hz
    simpa [hp] using he'
  | cons i α ih =>
    have hi : i ∈ I := hα i (by simp)
    have hα' : ∀ j ∈ α, j ∈ I := fun j hj => hα j (by simp [hj])
    have hr' : cs.IsReduced α := by simpa using hr.drop 1
    have hl1 := length_mul_of_left_minimal cs hxL (wordProd_mem_standard cs hα)
    have hl2 := length_mul_of_left_minimal cs hxL (wordProd_mem_standard cs hα')
    have hcancel : cs.simple i * (y * cs.wordProd β) = cs.wordProd α * x := by
      rw [← he, CoxeterSystem.wordProd_cons, mul_assoc,
        CoxeterSystem.simple_mul_simple_cancel_left]
    have hdesc : cs.length (cs.simple i * (y * cs.wordProd β)) <
        cs.length (y * cs.wordProd β) := by
      rw [hcancel, ← he, hl1, hl2, hr.eq, hr'.eq, List.length_cons]
      omega
    obtain ⟨η, hη, hpη⟩ := cs.exists_isReduced y
    have hd : cs.length (cs.simple i * cs.wordProd (η ++ β)) <
        cs.length (cs.wordProd (η ++ β)) := by
      simpa [CoxeterSystem.wordProd_append, ← hpη] using hdesc
    rcases simple_left_exchange_append cs hd with ⟨k, hk, hd⟩ | ⟨k, hk, hd⟩
    · have hs : cs.simple i * y = cs.wordProd (η.eraseIdx k) := by
        apply mul_right_cancel (b := cs.wordProd β)
        simpa [CoxeterSystem.wordProd_append, ← hpη, mul_assoc] using hd
      have hmin := hyL (cs.simple i) (simple_mem_standardSubgroup cs hi)
      rw [hs] at hmin
      have hbound := cs.length_wordProd_le (η.eraseIdx k)
      have hshort := List.length_eraseIdx_add_one hk
      have hlenη : cs.length y = η.length := by rw [hpη, hη.eq]
      omega
    · have he' : cs.wordProd α * x = y * cs.wordProd (β.eraseIdx k) := by
        have hd' : cs.simple i * (y * cs.wordProd β) =
            y * cs.wordProd (β.eraseIdx k) := by
          simpa [CoxeterSystem.wordProd_append, ← hpη] using hd
        exact hcancel.symm.trans hd'
      exact ih hα' hr' (β.eraseIdx k)
        (fun j hj => hβ j (List.mem_of_mem_eraseIdx hj)) he'

/-- The exact published uniqueness proposition for Coxeter parabolic double-coset minima. -/
theorem minimalRepresentativeUnique_proof : minimalRepresentativeUnique cs := by
  intro I J w x y hx hy hxmin hymin
  obtain ⟨ax, hax, bx, hbx, hex⟩ := hx
  obtain ⟨ay, hay, by', hby, hey⟩ := hy
  let a := ax * ay⁻¹
  let b := by'⁻¹ * bx
  have ha : a ∈ standardSubgroup cs I :=
    (standardSubgroup cs I).mul_mem hax ((standardSubgroup cs I).inv_mem hay)
  have hb : b ∈ standardSubgroup cs J :=
    (standardSubgroup cs J).mul_mem ((standardSubgroup cs J).inv_mem hby) hbx
  have he : x = a * y * b := by
    simp [a, b, hex, hey, mul_assoc]
  have hxy : cs.length x ≤ cs.length y := by
    have h := hxmin a⁻¹ ((standardSubgroup cs I).inv_mem ha)
      b⁻¹ ((standardSubgroup cs J).inv_mem hb)
    simpa [he, mul_assoc] using h
  have hyx : cs.length y ≤ cs.length x := by
    simpa [← he] using hymin a ha b hb
  have hlen : cs.length y = cs.length x := Nat.le_antisymm hyx hxy
  obtain ⟨α, hα, hr, hpα⟩ := reduced_standard_word_exists cs ha
  obtain ⟨β, hβ, hpβ⟩ := exists_standard_word cs ((standardSubgroup cs J).inv_mem hb)
  have hrel : cs.wordProd α * y = x * cs.wordProd β := by
    rw [hpα, hpβ, he]
    simp [mul_assoc]
  exact (eq_of_minimal_word_relation cs hymin hxmin hlen α hα hr β hβ hrel).symm

end
end Langlands.Group.RelativeWeylIndexing
