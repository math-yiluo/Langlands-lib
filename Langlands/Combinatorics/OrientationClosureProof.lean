import Langlands.Combinatorics.OrientationClosureStatement
import Mathlib.Data.Fintype.Basic

/-! # Finite orientation closure and its unique lattice extrema

Correcting finitely many disagreeing edges, one at a time, stays inside every
set of orientations closed under single-edge corrections toward the reference.
-/

namespace Langlands.Combinatorics

universe uE

section

variable {E : Type uE} [DecidableEq E] (o₀ : E → Bool)

/-- The orientation `o` corrected toward `o₀` on every edge of `T`. -/
private def correctOn (T : Finset E) (o : E → Bool) : E → Bool :=
  fun e => if e ∈ T then o₀ e else o e

/-- A set closed under single-edge corrections toward `o₀` contains every finite
correction of each of its members. -/
private theorem correctOn_mem {S : Set (E → Bool)}
    (hS : ∀ o ∈ S, ∀ e : E, o e ≠ o₀ e → Function.update o e (o₀ e) ∈ S)
    {o : E → Bool} (ho : o ∈ S) (T : Finset E) : correctOn o₀ T o ∈ S := by
  induction T using Finset.induction_on with
  | empty =>
    have h : correctOn o₀ ∅ o = o := by
      funext e
      simp [correctOn]
    rw [h]
    exact ho
  | insert a T ha ih =>
    by_cases hd : o a = o₀ a
    · have h : correctOn o₀ (insert a T) o = correctOn o₀ T o := by
        funext e
        by_cases he : e = a
        · subst he
          simp [correctOn, ha, hd]
        · simp [correctOn, he]
      rw [h]
      exact ih
    · have h : correctOn o₀ (insert a T) o =
          Function.update (correctOn o₀ T o) a (o₀ a) := by
        funext e
        by_cases he : e = a
        · subst he
          simp [correctOn]
        · simp [correctOn, he]
      rw [h]
      apply hS _ ih
      simpa [correctOn, ha] using hd

end

private theorem bool_ne_not_iff (a b : Bool) : a ≠ !b ↔ a = b := by
  revert a b
  decide

private theorem bool_not_of_ne (a b : Bool) (h : a ≠ b) : (!b) = a := by
  revert a b
  decide

/-- Zelevinsky's condition (★) in Boolean form: the closed sets of orientations
form a complete sublattice whose nonempty members contain the reference and whose
proper members omit the opposite orientation; the halfspaces meet in the
reference and cover everything but the opposite. -/
theorem orientationClosureExtrema : OrientationClosureExtremaStatement.{uE} := by
  intro E _ _ o₀ opposite H Closed
  refine ⟨?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro S hS
    constructor
    · constructor
      · rintro ⟨o, ho⟩
        have h := correctOn_mem o₀ hS ho Finset.univ
        have hu : correctOn o₀ Finset.univ o = o₀ := by
          funext e
          simp [correctOn]
        rwa [hu] at h
      · intro h
        exact ⟨o₀, h⟩
    · constructor
      · intro hne hopp
        apply hne
        apply Set.eq_univ_of_forall
        intro t
        have h := correctOn_mem o₀ hS hopp (Finset.univ.filter fun e => t e = o₀ e)
        have ht : correctOn o₀ (Finset.univ.filter fun e => t e = o₀ e) opposite = t := by
          funext e
          by_cases hte : t e = o₀ e
          · simp [correctOn, hte]
          · show (if e ∈ Finset.univ.filter fun e => t e = o₀ e then o₀ e else !(o₀ e)) = t e
            rw [ite_eq_right (by simpa using hte)]
            exact bool_not_of_ne _ _ hte
        rwa [ht] at h
      · intro hopp huniv
        apply hopp
        rw [huniv]
        exact Set.mem_univ _
  · intro o ho
    exact absurd ho (Set.notMem_empty o)
  · intro o _ e _
    exact Set.mem_univ _
  · intro o ho e he
    rw [Set.mem_singleton_iff] at ho
    subst ho
    exact absurd rfl he
  · intro o _ e _ h
    have h' := congrFun h e
    simp [opposite] at h'
  · intro a o ho e _
    show Function.update o e (o₀ e) a = o₀ a
    by_cases hae : a = e
    · subst hae
      simp
    · rw [Function.update_of_ne hae]
      exact ho
  · intro 𝒮 h𝒮
    constructor
    · intro o ho e he
      rw [Set.mem_sInter] at ho ⊢
      intro S hS
      exact h𝒮 S hS o (ho S hS) e he
    · intro o ho e he
      obtain ⟨S, hS, hoS⟩ := ho
      exact ⟨S, hS, h𝒮 S hS o hoS e he⟩
  · ext o
    simp only [Set.mem_iInter, Set.mem_singleton_iff]
    constructor
    · intro h
      funext e
      exact h e
    · intro h e
      rw [h]
      rfl
  · ext o
    simp only [Set.mem_iUnion, Set.mem_sdiff, Set.mem_univ, Set.mem_singleton_iff, true_and]
    constructor
    · rintro ⟨e, he⟩ h
      have h' := congrFun h e
      exact (bool_ne_not_iff _ _).mpr he h'
    · intro h
      by_contra hall
      apply h
      funext e
      by_contra h''
      exact hall ⟨e, (bool_ne_not_iff _ _).mp h''⟩

end Langlands.Combinatorics
