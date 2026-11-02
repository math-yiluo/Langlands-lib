import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.LinearIndependent.Defs

noncomputable section
universe u v w

namespace Langlands.GroupScheme.QuasiSplitUnitary

variable {K : Type u} [Field K] {n : Type v} [Fintype n] {α : Type w}

/-- The indices of the nonzero matrices in a family of projections. -/
def projectionSupport (P : α → Matrix n n K) : Set α := {a | P a ≠ 0}

/-- Orthogonal nonzero projections supply independent nonzero columns. -/
theorem projectionSupport_finite_and_card [DecidableEq α] (P : α → Matrix n n K)
    (hP : ∀ a b, P a * P b = if a = b then P a else 0) :
    (projectionSupport P).Finite ∧
      Nat.card (projectionSupport P) ≤ Fintype.card n := by
  classical
  have hcol : ∀ a : projectionSupport P, ∃ j : n, (fun i => P a.val i j) ≠ 0 := by
    intro a
    by_contra! h
    apply a.property
    ext i j
    exact congrFun (h j) i
  choose j hj using hcol
  let v : projectionSupport P → n → K := fun a i => P a.val i (j a)
  have hv : ∀ a, v a ≠ 0 := hj
  have hproj (a b : projectionSupport P) :
      (P a.val).mulVecLin (v b) = if a = b then v a else 0 := by
    have h := hP a.val b.val
    by_cases hab : a = b
    · subst b
      simp only [ite_true] at h ⊢
      funext i
      exact congrArg (fun M : Matrix n n K => M i (j a)) h
    · have hab' : a.val ≠ b.val := fun h => hab (Subtype.ext h)
      simp only [ite_eq_right hab', ite_eq_right hab] at h ⊢
      funext i
      exact congrArg (fun M : Matrix n n K => M i (j b)) h
  have hli : LinearIndependent K v := by
    rw [linearIndependent_iff']
    intro s l hsum a ha
    have h := congrArg (P a.val).mulVecLin hsum
    rw [map_sum, map_zero] at h
    simp only [map_smul, hproj] at h
    have hs : l a • v a = 0 := by
      simpa [Finset.sum_ite_eq', ha] using h
    exact (smul_eq_zero.mp hs).resolve_right (hv a)
  let : Finite (projectionSupport P) := hli.finite
  let := Fintype.ofFinite (projectionSupport P)
  refine ⟨Set.toFinite _, ?_⟩
  simpa only [Nat.card_eq_fintype_card, Module.finrank_pi, Module.finrank_self,
    Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] using
    hli.fintype_card_le_finrank

variable {I : Type w} [Fintype I]

/-- A negation-stable set of at most two integer weights lies in a single pair. -/
theorem two_weights_in_neg_pair (S : Set (I → ℤ)) (hS : S.Finite)
    (hcard : Nat.card S ≤ 2) (hneg : ∀ a ∈ S, -a ∈ S) :
    ∃ a : I → ℤ, ∀ b ∈ S, b = a ∨ b = -a := by
  classical
  let := hS.fintype
  by_cases hn : ∃ a ∈ S, a ≠ 0
  · obtain ⟨a, ha, ha0⟩ := hn
    refine ⟨a, ?_⟩
    intro b hb
    by_contra! h
    have han : a ≠ -a := by
      intro heq
      apply ha0
      funext i
      have hi := congrFun heq i
      simp only [Pi.neg_apply] at hi
      change a i = 0
      omega
    let f : Fin 3 → S := ![⟨a, ha⟩, ⟨-a, hneg a ha⟩, ⟨b, hb⟩]
    have hf : Function.Injective f := by
      intro i j hij
      have heq := congrArg Subtype.val hij
      fin_cases i <;> fin_cases j <;>
        simp_all [f, Ne.symm]
    have hc := Nat.card_le_card_of_injective f hf
    have : 3 ≤ Nat.card S := by simpa using hc
    omega
  · refine ⟨0, fun b hb => Or.inl ?_⟩
    by_contra hb0
    exact hn ⟨b, hb, hb0⟩

end Langlands.GroupScheme.QuasiSplitUnitary
