import Langlands.LinearAlgebra.BoundedMatrixPowers
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! # Bounded actions on a spanning set -/

noncomputable section

universe u v

open ValuativeRel

namespace Langlands.LinearAlgebra

section Valuation

variable {F : Type*} [Field F] [ValuativeRel F]

/-- Pointwise uniform bounds for a family of linear forms extend to the span. -/
theorem exists_valuative_bound_linearMap_of_mem_span
    {V I : Type*} [AddCommGroup V] [Module F V]
    (S : Set V) (L : I → V →ₗ[F] F)
    (hS : ∀ x ∈ S, ∃ b : F, b ≠ 0 ∧ ∀ i, L i x ≤ᵥ b)
    {x : V} (hx : x ∈ Submodule.span F S) :
    ∃ b : F, b ≠ 0 ∧ ∀ i, L i x ≤ᵥ b := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact hS x hx
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨b, hb, hx⟩ := hx
    obtain ⟨c, hc, hy⟩ := hy
    rcases vle_total b c with hbc | hcb
    · exact ⟨c, hc, fun i ↦ by
        rw [map_add]
        exact vle_add ((hx i).trans hbc) (hy i)⟩
    · exact ⟨b, hb, fun i ↦ by
        rw [map_add]
        exact vle_add (hx i) ((hy i).trans hcb)⟩
  | smul a x _ hx =>
    by_cases ha : a = 0
    · subst a
      exact ⟨1, one_ne_zero, by simp⟩
    obtain ⟨b, hb, hx⟩ := hx
    refine ⟨a * b, mul_ne_zero ha hb, fun i ↦ ?_⟩
    simpa only [map_smul, smul_eq_mul] using mul_vle_mul_right (hx i) a

/-- A finite family of nonzero scalar bounds has a common nonzero bound. -/
theorem exists_common_valuative_bound
    {I : Type*} [Fintype I] (b : I → F) (hb : ∀ i, b i ≠ 0) :
    ∃ c : F, c ≠ 0 ∧ ∀ i, b i ≤ᵥ c := by
  classical
  have h : ∀ s : Finset I, ∃ c : F, c ≠ 0 ∧ ∀ i ∈ s, b i ≤ᵥ c := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨1, one_ne_zero, by simp⟩
    | @insert i s _ ih =>
      obtain ⟨c, hc, hs⟩ := ih
      rcases vle_total (b i) c with hi | hi
      · refine ⟨c, hc, ?_⟩
        intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact hi
        · exact hs j hj
      · refine ⟨b i, hb i, ?_⟩
        intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact vle_rfl
        · exact (hs j hj).trans hi
  obtain ⟨c, hc, hs⟩ := h Finset.univ
  exact ⟨c, hc, fun i ↦ hs i (Finset.mem_univ i)⟩

/-- All matrices preserving one bounded spanning set have a common entry bound. -/
theorem exists_valuative_bound_entries_of_mapsTo_spanning
    {n I : Type*} [Fintype n] [DecidableEq n]
    (S : Set (n → F)) (hspan : Submodule.span F S = ⊤)
    (hS : ∀ i, ∃ b : F, b ≠ 0 ∧ ∀ x ∈ S, x i ≤ᵥ b)
    (A : I → Matrix n n F) (hA : ∀ k, Set.MapsTo (A k).mulVec S S) :
    ∃ b : F, b ≠ 0 ∧ ∀ k i j, A k i j ≤ᵥ b := by
  classical
  have hentry : ∀ i j : n, ∃ b : F, b ≠ 0 ∧ ∀ k, A k i j ≤ᵥ b := by
    intro i j
    have hsingle : Pi.single j (1 : F) ∈ Submodule.span F S := by
      rw [hspan]
      exact Submodule.mem_top
    have hforms : ∀ x ∈ S, ∃ b : F, b ≠ 0 ∧
        ∀ k, ((LinearMap.proj i).comp (A k).mulVecLin) x ≤ᵥ b := by
      intro x hx
      obtain ⟨b, hb, h⟩ := hS i
      exact ⟨b, hb, fun k ↦ h _ (hA k hx)⟩
    obtain ⟨b, hb, h⟩ := exists_valuative_bound_linearMap_of_mem_span S
      (fun k ↦ (LinearMap.proj i).comp (A k).mulVecLin) hforms hsingle
    refine ⟨b, hb, fun k ↦ ?_⟩
    simpa only [LinearMap.comp_apply, LinearMap.proj_apply,
      Matrix.mulVecLin_apply, Matrix.mulVec_single_one, Matrix.col_apply] using h k
  choose b hb hbound using hentry
  obtain ⟨c, hc, h⟩ := exists_common_valuative_bound
    (fun ij : n × n ↦ b ij.1 ij.2) (fun ij ↦ hb ij.1 ij.2)
  exact ⟨c, hc, fun k i j ↦ (hbound i j k).trans (h (i, j))⟩

/-- The nonnegative powers of a matrix preserving a bounded spanning set are bounded. -/
theorem exists_valuative_bound_powers_of_mapsTo_spanning
    {n : Type*} [Fintype n] [DecidableEq n]
    (S : Set (n → F)) (hspan : Submodule.span F S = ⊤)
    (hS : ∀ i, ∃ b : F, b ≠ 0 ∧ ∀ x ∈ S, x i ≤ᵥ b)
    (A : Matrix n n F) (hA : Set.MapsTo A.mulVec S S) :
    ∃ b : F, b ≠ 0 ∧ ∀ k : ℕ, ∀ i j, (A ^ k) i j ≤ᵥ b := by
  apply exists_valuative_bound_entries_of_mapsTo_spanning S hspan hS (fun k : ℕ ↦ A ^ k)
  intro k
  induction k with
  | zero =>
    intro x hx
    simpa only [pow_zero, Matrix.one_mulVec] using hx
  | succ k hk =>
    intro x hx
    rw [pow_succ', ← Matrix.mulVec_mulVec]
    exact hA (hk hx)

end Valuation

/-- A matrix preserving a coordinate-bounded spanning set has integral characteristic
coefficients over a nonarchimedean local field. No invertibility is assumed. -/
def BoundedSpanningActionStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (n : Type v) [Fintype n] [DecidableEq n]
    (S : Set (n → F)), Submodule.span F S = ⊤ →
    (∀ i, ∃ b : F, b ≠ 0 ∧ ∀ x ∈ S, x i ≤ᵥ b) →
    ∀ (A : Matrix n n F), Set.MapsTo A.mulVec S S →
      ∀ d : ℕ, A.charpoly.coeff d ≤ᵥ (1 : F)

/-- Integral characteristic coefficients for an action on a bounded spanning set. -/
theorem boundedSpanningAction : BoundedSpanningActionStatement.{u,v} := by
  intro F _ _ _ _ n _ _ S hspan hS A hA d
  exact charpoly_coeff_vle_one_of_bounded_powers A
    (exists_valuative_bound_powers_of_mapsTo_spanning S hspan hS A hA) d

end Langlands.LinearAlgebra
