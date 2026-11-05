import Langlands.GroupScheme.Rational.RelativeRootMultiples
import Mathlib.LinearAlgebra.RootSystem.BaseExists

/-! # Restricting a root pairing to indivisible roots -/

noncomputable section

open Set Submodule

namespace RootPairing

variable {J M N : Type*} [AddCommGroup M] [Module ℚ M]
    [AddCommGroup N] [Module ℚ N] (P : RootPairing J ℚ M N)

/-- Indivisibility is tested inside the root set, rather than the ambient lattice. -/
def indivisibleIndices : Set J :=
  {a | ∀ (b : J) (n : ℕ), 2 ≤ n → P.root a ≠ n • P.root b}

theorem indivisibleIndices_reflection_iff (a b : J) :
    P.reflectionPerm a b ∈ P.indivisibleIndices ↔ b ∈ P.indivisibleIndices := by
  have hpres (b : J) (hb : b ∈ P.indivisibleIndices) :
      P.reflectionPerm a b ∈ P.indivisibleIndices := by
    intro c n hn heq
    have h := congrArg (P.reflection a) heq
    simp only [root_reflectionPerm, reflection_same, map_nsmul] at h
    exact hb (P.reflectionPerm a c) n hn (by simpa only [root_reflectionPerm] using h)
  exact ⟨fun h => by simpa using hpres _ h, hpres b⟩

/-- The roots and coroots indexed by indivisible roots form a root pairing. -/
def indivisiblePairing : RootPairing P.indivisibleIndices ℚ M N where
  toLinearMap := P.toLinearMap
  root := (Function.Embedding.subtype _).trans P.root
  coroot := (Function.Embedding.subtype _).trans P.coroot
  root_coroot_two a := P.root_coroot_two a.val
  reflectionPerm a := (P.reflectionPerm a.val).subtypeEquiv
    (fun b => (P.indivisibleIndices_reflection_iff a.val b).symm)
  reflectionPerm_root a b := P.reflectionPerm_root a.val b.val
  reflectionPerm_coroot a b := P.reflectionPerm_coroot a.val b.val

@[simp] theorem indivisiblePairing_root (a : P.indivisibleIndices) :
    P.indivisiblePairing.root a = P.root a.val := rfl

instance [P.IsCrystallographic] : P.indivisiblePairing.IsCrystallographic where
  exists_value a b := P.exists_value a.val b.val

variable [P.IsCrystallographic]

/-- A positive indecomposable root is indivisible, also in a nonreduced pairing. -/
theorem mem_indivisibleIndices_of_mem_baseOf (f : M →+ ℚ) {a : J}
    (ha : a ∈ IsAddIndecomposable.baseOf P.root f) : a ∈ P.indivisibleIndices := by
  intro b n hn hab
  rcases P.eq_one_or_two_of_root_eq_nsmul hab with h | h
  · omega
  · subst n
    have hb : 0 < f (P.root b) := by
      have hpos := ha.1
      change 0 < f (P.root a) at hpos
      rw [hab, map_nsmul, nsmul_eq_mul] at hpos
      norm_num at hpos
      linarith
    have hsum : P.root a = P.root b + P.root b := by simpa only [two_smul] using hab
    rcases ha.2 b hb b hb hsum with hzero | hzero <;> exact P.ne_zero b hzero

variable [Finite J]

/-- Passing to the indivisible roots does not change the positive indecomposable roots. -/
theorem image_baseOf_indivisiblePairing (f : M →+ ℚ)
    (hf : ∀ a, f (P.root a) ≠ 0) :
    P.indivisiblePairing.root '' IsAddIndecomposable.baseOf P.indivisiblePairing.root f =
      P.root '' IsAddIndecomposable.baseOf P.root f := by
  classical
  let Q := P.indivisiblePairing
  let A := P.root '' IsAddIndecomposable.baseOf P.root f
  let B := Q.root '' IsAddIndecomposable.baseOf Q.root f
  have hAB : A ⊆ B := by
    rintro _ ⟨a, ha, rfl⟩
    let a' : P.indivisibleIndices := ⟨a, P.mem_indivisibleIndices_of_mem_baseOf f ha⟩
    refine ⟨a', ⟨ha.1, ?_⟩, rfl⟩
    intro b hb c hc heq
    exact ha.2 b.val hb c.val hc heq
  have hli : LinearIndepOn ℚ id B := by
    have hQ := Q.linearIndepOn_root_baseOf' f.toRatLinearMap
      (fun a => hf a.val)
    exact hQ.id_image
  have hspan : B ⊆ Submodule.span ℚ A := by
    rintro _ ⟨a, ha, rfl⟩
    let := P.indexNeg
    rcases IsAddIndecomposable.mem_or_neg_mem_closure_baseOf P.root f a.val
      (hf a.val) (by simp) with h | h
    · exact Submodule.closure_subset_span h
    · exact (Submodule.span ℚ A).neg_mem_iff.mp (Submodule.closure_subset_span h)
  exact eq_of_linearIndepOn_id_of_span_subtype hli hAB hspan

end RootPairing
