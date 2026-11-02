import Langlands.Group.RelativeWeylIndexingTargets
import Langlands.Group.RelativeWeylExchange

/-!
# The double-coset minimum length criterion

Exchange gives length additivity at a one-sided coset minimum. Applying that
additivity on both sides compares any element with no specified simple descents
to a least-length element in its double coset.
-/

namespace Langlands.Group.RelativeWeylIndexing

universe u v
variable {B : Type u} {W : Type v} [Group W]
variable {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

open Classical
noncomputable section

private theorem wordProd_mem_standard {I : Finset B} {ω : List B}
    (hω : ∀ i ∈ ω, i ∈ I) : cs.wordProd ω ∈ standardSubgroup cs I := by
  induction ω with
  | nil => simp
  | cons i ω ih =>
    rw [CoxeterSystem.wordProd_cons]
    exact (standardSubgroup cs I).mul_mem
      (simple_mem_standardSubgroup cs (hω i (by simp)))
      (ih (fun j hj => hω j (by simp [hj])))

private theorem exists_standard_word {I : Finset B} {a : W}
    (ha : a ∈ standardSubgroup cs I) :
    ∃ ω : List B, (∀ i ∈ ω, i ∈ I) ∧ cs.wordProd ω = a := by
  induction ha using Subgroup.closure_induction with
  | mem a ha =>
    obtain ⟨i, hi, rfl⟩ := ha
    exact ⟨[i], by simpa, by simp⟩
  | one => exact ⟨[], by simp, by simp⟩
  | mul a b ha hb iha ihb =>
    obtain ⟨α, hα, rfl⟩ := iha
    obtain ⟨β, hβ, rfl⟩ := ihb
    refine ⟨α ++ β, ?_, cs.wordProd_append α β⟩
    intro i hi
    exact (List.mem_append.mp hi).elim (hα i) (hβ i)
  | inv a ha ih =>
    obtain ⟨ω, hω, rfl⟩ := ih
    exact ⟨ω.reverse, by simpa using hω, cs.wordProd_reverse ω⟩

private theorem exists_shortest_standard_word {I : Finset B} {a : W}
    (ha : a ∈ standardSubgroup cs I) :
    ∃ ω : List B, (∀ i ∈ ω, i ∈ I) ∧ cs.wordProd ω = a ∧
      ∀ η : List B, (∀ i ∈ η, i ∈ I) → cs.wordProd η = a → ω.length ≤ η.length := by
  have hex : ∃ n : ℕ, ∃ ω : List B,
      (∀ i ∈ ω, i ∈ I) ∧ cs.wordProd ω = a ∧ ω.length = n := by
    obtain ⟨ω, hω, hp⟩ := exists_standard_word cs ha
    exact ⟨ω.length, ω, hω, hp, rfl⟩
  obtain ⟨ω, hω, hp, hl⟩ := Nat.find_spec hex
  refine ⟨ω, hω, hp, ?_⟩
  intro η hη he
  rw [hl]
  exact Nat.find_min' hex ⟨η, hη, he, rfl⟩

/-- A shortest word on `I` adds its length to a left-coset minimum. -/
private theorem shortest_word_length_add {I : Finset B} {w : W}
    (hw : ∀ a ∈ standardSubgroup cs I, cs.length w ≤ cs.length (a * w))
    (α : List B) (hα : ∀ i ∈ α, i ∈ I)
    (hmin : ∀ γ : List B, (∀ i ∈ γ, i ∈ I) →
      cs.wordProd γ = cs.wordProd α → α.length ≤ γ.length) :
    cs.length (cs.wordProd α * w) = α.length + cs.length w := by
  induction α with
  | nil => simp
  | cons i α ih =>
    have hi : i ∈ I := hα i (by simp)
    have hα' : ∀ j ∈ α, j ∈ I := fun j hj => hα j (by simp [hj])
    have hmα : ∀ γ : List B, (∀ j ∈ γ, j ∈ I) →
        cs.wordProd γ = cs.wordProd α → α.length ≤ γ.length := by
      intro γ hγ hp
      have hm := hmin (i :: γ) (by simpa using And.intro hi hγ)
        (by simp only [CoxeterSystem.wordProd_cons, hp])
      simpa using hm
    have hlen := ih hα' hmα
    rw [CoxeterSystem.wordProd_cons, mul_assoc]
    rcases cs.length_simple_mul (cs.wordProd α * w) i with hu | hd
    · rw [hu, hlen, List.length_cons]
      omega
    · have hdesc : cs.length (cs.simple i * (cs.wordProd α * w)) <
          cs.length (cs.wordProd α * w) := by omega
      obtain ⟨η, hη, hpη⟩ := cs.exists_isReduced w
      have hd' : cs.length (cs.simple i * cs.wordProd (α ++ η)) <
          cs.length (cs.wordProd (α ++ η)) := by
        simpa [CoxeterSystem.wordProd_append, ← hpη] using hdesc
      rcases simple_left_exchange_append cs hd' with ⟨k, hk, he⟩ | ⟨k, hk, he⟩
      -- Deletion in the parabolic word contradicts its chosen shortest length.
      · have he' : cs.wordProd (α.eraseIdx k) = cs.wordProd (i :: α) := by
          apply mul_right_cancel (b := w)
          simpa [CoxeterSystem.wordProd_append, CoxeterSystem.wordProd_cons,
            ← hpη, mul_assoc] using he.symm
        have hm := hmin (α.eraseIdx k)
          (fun j hj => hα' j (List.mem_of_mem_eraseIdx hj)) he'
        have hl := List.length_eraseIdx_add_one hk
        simp only [List.length_cons] at hm
        omega
      -- Deletion in the reduced word for w contradicts coset minimality.
      · let a := (cs.wordProd α)⁻¹ * cs.simple i * cs.wordProd α
        have ha : a ∈ standardSubgroup cs I :=
          (standardSubgroup cs I).mul_mem
            ((standardSubgroup cs I).mul_mem
              ((standardSubgroup cs I).inv_mem (wordProd_mem_standard cs hα'))
              (simple_mem_standardSubgroup cs hi))
            (wordProd_mem_standard cs hα')
        have he' : a * w = cs.wordProd (η.eraseIdx k) := by
          have he0 : cs.simple i * (cs.wordProd α * w) =
              cs.wordProd α * cs.wordProd (η.eraseIdx k) := by
            simpa [CoxeterSystem.wordProd_append, ← hpη] using he
          have he1 := congrArg (fun z : W => (cs.wordProd α)⁻¹ * z) he0
          simpa [a, mul_assoc] using he1
        have hbound := hw a ha
        rw [he'] at hbound
        have hl := cs.length_wordProd_le (η.eraseIdx k)
        have hlη := List.length_eraseIdx_add_one hk
        have hr : cs.length w = η.length := by rw [hpη, hη.eq]
        omega

/-- Multiplication by a standard subgroup adds length at a left-coset minimum. -/
theorem length_mul_of_left_minimal {I : Finset B} {w a : W}
    (hw : ∀ x ∈ standardSubgroup cs I, cs.length w ≤ cs.length (x * w))
    (ha : a ∈ standardSubgroup cs I) :
    cs.length (a * w) = cs.length a + cs.length w := by
  obtain ⟨α, hα, hp, hm⟩ := exists_shortest_standard_word cs ha
  have h1 := shortest_word_length_add cs (w := 1) (I := I) (by simp) α hα
    (by simpa [hp] using hm)
  have h2 := shortest_word_length_add cs hw α hα (by simpa [hp] using hm)
  simpa [hp] using h2.trans (by simpa [hp] using congrArg (· + cs.length w) h1.symm)

/-- Least Coxeter length exists in every double coset without ambient finiteness. -/
theorem exists_minimal_in_doubleCoset_unrestricted (I J : Finset B) (w : W) :
    ∃ x ∈ doubleCoset cs I J w, IsMinimal cs I J x := by
  have hex : ∃ n : ℕ, ∃ x : W,
      x ∈ doubleCoset cs I J w ∧ cs.length x = n :=
    ⟨cs.length w, w, mem_doubleCoset_self cs I J w, rfl⟩
  obtain ⟨x, hx, hl⟩ := Nat.find_spec hex
  refine ⟨x, hx, ?_⟩
  intro a ha b hb
  rw [hl]
  exact Nat.find_min' hex ⟨a * x * b, mul_mem_doubleCoset cs hx ha hb, rfl⟩

/-- Absence of simple left descents implies least length in the whole left coset. -/
theorem left_minimal_of_simple {I : Finset B} {w : W}
    (hw : ∀ i ∈ I, cs.length w < cs.length (cs.simple i * w)) :
    ∀ a ∈ standardSubgroup cs I, cs.length w ≤ cs.length (a * w) := by
  obtain ⟨v, hvdc, hv⟩ := exists_minimal_in_doubleCoset_unrestricted cs I ∅ w
  obtain ⟨a, ha, b, hb, he⟩ := hvdc
  have hb1 : b = 1 := by simpa using hb
  subst b
  simp only [mul_one] at he
  have hvL : ∀ x ∈ standardSubgroup cs I, cs.length v ≤ cs.length (x * v) := by
    intro x hx
    simpa using hv x hx 1 (standardSubgroup cs ∅).one_mem
  obtain ⟨α, hα, hp, hm⟩ := exists_shortest_standard_word cs
    ((standardSubgroup cs I).inv_mem ha)
  have hwe : w = cs.wordProd α * v := by
    rw [hp, he]
    simp
  have hlen := shortest_word_length_add cs hvL α hα (by simpa [hp] using hm)
  cases α with
  | nil =>
    have hwv : w = v := by simpa using hwe
    simpa [hwv] using hvL
  | cons i α =>
    have hi := hw i (hα i (by simp))
    have hcancel : cs.simple i * w = cs.wordProd α * v := by
      rw [hwe, CoxeterSystem.wordProd_cons, mul_assoc,
        CoxeterSystem.simple_mul_simple_cancel_left]
    have hlw : cs.length w = α.length + 1 + cs.length v := by
      rw [hwe, hlen, List.length_cons]
    have hbound := cs.length_mul_le (cs.wordProd α) v
    have hword := cs.length_wordProd_le α
    rw [hcancel] at hi
    omega

/-- Right multiplication adds length at a right-coset minimum. -/
theorem length_mul_of_right_minimal {J : Finset B} {w b : W}
    (hw : ∀ x ∈ standardSubgroup cs J, cs.length w ≤ cs.length (w * x))
    (hb : b ∈ standardSubgroup cs J) :
    cs.length (w * b) = cs.length w + cs.length b := by
  have hwI : ∀ x ∈ standardSubgroup cs J,
      cs.length w⁻¹ ≤ cs.length (x * w⁻¹) := by
    intro x hx
    have h := hw x⁻¹ ((standardSubgroup cs J).inv_mem hx)
    simpa only [← cs.length_inv (w * x⁻¹), mul_inv_rev, inv_inv,
      cs.length_inv w] using h
  have h := length_mul_of_left_minimal cs hwI
    ((standardSubgroup cs J).inv_mem hb)
  simpa only [← mul_inv_rev, cs.length_inv, add_comm] using h

/-- Absence of simple right descents implies least length in the whole right coset. -/
theorem right_minimal_of_simple {J : Finset B} {w : W}
    (hw : ∀ j ∈ J, cs.length w < cs.length (w * cs.simple j)) :
    ∀ b ∈ standardSubgroup cs J, cs.length w ≤ cs.length (w * b) := by
  have hwI : ∀ j ∈ J, cs.length w⁻¹ < cs.length (cs.simple j * w⁻¹) := by
    intro j hj
    simpa only [← cs.length_inv (w * cs.simple j), mul_inv_rev,
      CoxeterSystem.inv_simple, cs.length_inv w] using hw j hj
  intro b hb
  have h := left_minimal_of_simple cs hwI b⁻¹ ((standardSubgroup cs J).inv_mem hb)
  simpa only [← mul_inv_rev, cs.length_inv] using h

/-- The published Coxeter double-coset minimum length criterion, with no finiteness premise. -/
theorem minimalityLengthCriterion_proof : minimalityLengthCriterion cs := by
  intro I J w
  constructor
  · intro hw
    constructor
    · intro i hi
      have h := hw (cs.simple i) (simple_mem_standardSubgroup cs hi)
        1 (standardSubgroup cs J).one_mem
      simp only [mul_one] at h
      have hn := cs.length_simple_mul_ne w i
      omega
    · intro j hj
      have h := hw 1 (standardSubgroup cs I).one_mem
        (cs.simple j) (simple_mem_standardSubgroup cs hj)
      simp only [one_mul] at h
      have hn := cs.length_mul_simple_ne w j
      omega
  · rintro ⟨hwL, hwR⟩
    have hwL' := left_minimal_of_simple cs hwL
    have hwR' := right_minimal_of_simple cs hwR
    obtain ⟨v, hvdc, hv⟩ := exists_minimal_in_doubleCoset_unrestricted cs I J w
    obtain ⟨a, ha, b, hb, he⟩ := hvdc
    have hvL : ∀ x ∈ standardSubgroup cs I,
        cs.length v ≤ cs.length (x * v) := by
      intro x hx
      simpa using hv x hx 1 (standardSubgroup cs J).one_mem
    have hvR : ∀ x ∈ standardSubgroup cs J,
        cs.length v ≤ cs.length (v * x) := by
      intro x hx
      simpa using hv 1 (standardSubgroup cs I).one_mem x hx
    have h1 := length_mul_of_left_minimal cs hwL' ha
    have h2 := length_mul_of_right_minimal cs hvR
      ((standardSubgroup cs J).inv_mem hb)
    have h3 := length_mul_of_right_minimal cs hwR' hb
    have h4 := length_mul_of_left_minimal cs hvL
      ((standardSubgroup cs I).inv_mem ha)
    have h2' : cs.length (a * w) = cs.length v + cs.length b := by
      simpa [he, mul_assoc] using h2
    have h4' : cs.length (w * b) = cs.length a + cs.length v := by
      simpa [he, mul_assoc] using h4
    -- The two equations have opposite differences of parabolic lengths.
    have heq : cs.length w = cs.length v := by omega
    intro x hx y hy
    have h := hv (x * a⁻¹)
      ((standardSubgroup cs I).mul_mem hx ((standardSubgroup cs I).inv_mem ha))
      (b⁻¹ * y)
      ((standardSubgroup cs J).mul_mem ((standardSubgroup cs J).inv_mem hb) hy)
    rw [← heq] at h
    simpa [he, mul_assoc] using h

end
end Langlands.Group.RelativeWeylIndexing
