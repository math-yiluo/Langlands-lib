import Langlands.LinearAlgebra.ArthurCombinatorics
import Mathlib.LinearAlgebra.RootSystem.Finite.Nondegenerate

/-!
# The inverse of a Cartan block has nonnegative entries

For a finite crystallographic root system over `ℝ` with a base `b` and `Θ ⊆ b.support`, every
entry of `(cartanBlock P Θ)⁻¹` is nonnegative. Equivalently, each weight
`weightCoordinate P Θ i` is a nonnegative combination of the simple roots `α_k`, `k ∈ Θ`
("the positive chamber lies in the cone of positive roots").

The proof is the Stieltjes-matrix argument for the canonical form `P.RootForm`, which is
positive definite on the span of the roots and nonpositive on pairs of distinct simple roots.
-/

noncomputable section

set_option autoImplicit false

namespace Langlands.ArthurCombinatorics

open Finset

variable {ι M N : Type*} [DecidableEq ι] [Fintype ι] [AddCommGroup M] [Module ℝ M]
  [AddCommGroup N] [Module ℝ N] {P : RootPairing ι ℝ M N} [P.IsRootSystem]
  [P.IsCrystallographic] (b : P.Base)

omit [DecidableEq ι] [P.IsRootSystem] in
/-- Distinct simple roots pair nonpositively. -/
theorem pairing_nonpos_of_ne {i j : ι} (hij : i ≠ j) (hi : i ∈ b.support) (hj : j ∈ b.support) :
    P.pairing i j ≤ 0 := by
  have h := b.pairingIn_le_zero_of_ne hij hi hj
  rw [← P.algebraMap_pairingIn ℤ, algebraMap_int_eq, eq_intCast]
  exact_mod_cast h

omit [DecidableEq ι] [P.IsRootSystem] [P.IsCrystallographic] in
/-- The canonical form on two roots, through the Cartan integer. -/
theorem rootForm_root_root (k j : ι) :
    P.RootForm (P.root k) (P.root j) = P.pairing k j * (P.RootForm (P.root j) (P.root j) / 2) := by
  have h := P.toInvariantForm.two_mul_apply_root_root k j
  simp only [RootPairing.toInvariantForm_form] at h
  linarith

omit [DecidableEq ι] [P.IsRootSystem] [P.IsCrystallographic] in
theorem rootForm_root_self_pos (j : ι) : 0 < P.RootForm (P.root j) (P.root j) :=
  P.rootForm_pos_of_ne_zero (Submodule.subset_span ⟨j, rfl⟩) (P.ne_zero j)

omit [DecidableEq ι] [P.IsRootSystem] in
/-- Distinct simple roots are nonpositive for the canonical form. -/
theorem rootForm_simple_nonpos {k j : ι} (hkj : k ≠ j) (hk : k ∈ b.support)
    (hj : j ∈ b.support) : P.RootForm (P.root k) (P.root j) ≤ 0 := by
  rw [rootForm_root_root]
  exact mul_nonpos_of_nonpos_of_nonneg (pairing_nonpos_of_ne b hkj hk hj)
    (div_nonneg (rootForm_root_self_pos j).le zero_le_two)

omit [P.IsRootSystem] in
/-- **Stieltjes argument.** If `x = ∑_{k ∈ Θ} w_k α_k` has `B(x, α_j) ≥ 0` for every `j ∈ Θ`,
then every `w_k ≥ 0`. -/
theorem nonneg_of_rootForm_nonneg {Θ : Finset ι} (hΘ : Θ ⊆ b.support) (w : Θ → ℝ)
    (hw : ∀ j : Θ, 0 ≤ P.RootForm (∑ k : Θ, w k • P.root k) (P.root j)) (k : Θ) :
    0 ≤ w k := by
  let z : Θ → ℝ := fun k => max (-w k) 0
  let p : Θ → ℝ := fun k => max (w k) 0
  let v : (Θ → ℝ) → M := fun x => ∑ k : Θ, x k • P.root k
  have hz : ∀ k, 0 ≤ z k := fun k => le_max_right _ _
  have hp : ∀ k, 0 ≤ p k := fun k => le_max_right _ _
  have hwpz : ∀ k, w k = p k - z k := fun k => (max_zero_sub_max_neg_zero_eq_self (w k)).symm
  have hzp : ∀ k, z k * p k = 0 := by
    intro k
    rcases le_total (w k) 0 with h | h
    · simp [p, max_eq_right h]
    · simp [z, max_eq_right (neg_nonpos.mpr h)]
  have hleft : ∀ (x : Θ → ℝ) (y : M), P.RootForm (v x) y = ∑ k, x k * P.RootForm (P.root k) y := by
    intro x y
    simp only [v, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  have hright : ∀ (y : M) (x : Θ → ℝ), P.RootForm y (v x) = ∑ k, x k * P.RootForm y (P.root k) := by
    intro y x
    simp only [v, map_sum, map_smul, smul_eq_mul]
  have hsymm : ∀ x y : M, P.RootForm x y = P.RootForm y x := fun x y =>
    (LinearMap.IsSymm.eq P.rootForm_symmetric x y).trans (by rfl)
  have hv : v w = v p - v z := by
    simp only [v, hwpz, sub_smul, Finset.sum_sub_distrib]
  -- `B(v z, v w) ≥ 0`
  have h₁ : 0 ≤ P.RootForm (v z) (v w) := by
    rw [hleft]
    refine Finset.sum_nonneg fun j _ => mul_nonneg (hz j) ?_
    rw [hsymm]
    exact hw j
  -- `B(v z, v p) ≤ 0`
  have h₂ : P.RootForm (v z) (v p) ≤ 0 := by
    rw [hleft]
    refine Finset.sum_nonpos fun j _ => ?_
    rw [hright, Finset.mul_sum]
    refine Finset.sum_nonpos fun l _ => ?_
    by_cases hjl : j = l
    · subst hjl
      rw [← mul_assoc, mul_comm (z j) (p j), mul_comm (p j) (z j), hzp, zero_mul]
    · have hne : (j : ι) ≠ l := fun h => hjl (Subtype.ext h)
      have hB := rootForm_simple_nonpos b hne (hΘ j.2) (hΘ l.2)
      rw [← mul_assoc]
      exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (hz j) (hp l)) hB
  -- hence `B(v z, v z) ≤ 0`
  have h₃ : P.RootForm (v z) (v z) ≤ 0 := by
    have hsub : P.RootForm (v z) (v w) = P.RootForm (v z) (v p) - P.RootForm (v z) (v z) := by
      rw [hv, map_sub]
    linarith
  have h₄ : P.RootForm (v z) (v z) = 0 := le_antisymm h₃ (P.zero_le_rootForm _)
  have hspan : v z ∈ P.rootSpan ℝ :=
    Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  have h₅ : v z = 0 := P.eq_zero_of_mem_rootSpan_of_rootForm_self_eq_zero hspan h₄
  have hli : LinearIndependent ℝ (fun k : Θ => P.root (k : ι)) :=
    b.linearIndepOn_root.mono (by exact_mod_cast hΘ)
  have hzk : z k = 0 := Fintype.linearIndependent_iff.mp hli z h₅ k
  rw [hwpz, hzk, sub_zero]
  exact hp k

/-- **The inverse of a Cartan block has nonnegative entries.** -/
theorem cartanBlock_inv_nonneg {Θ : Finset ι} (hΘ : Θ ⊆ b.support) (i k : Θ) :
    0 ≤ (cartanBlock P Θ)⁻¹ i k := by
  have hinv := Matrix.nonsing_inv_mul (cartanBlock P Θ) (isUnit_det_cartanBlock b hΘ)
  refine nonneg_of_rootForm_nonneg b hΘ (fun k => (cartanBlock P Θ)⁻¹ i k) (fun j => ?_) k
  have hkj : ∀ l : Θ, P.RootForm (P.root l) (P.root j) =
      cartanBlock P Θ l j * (P.RootForm (P.root j) (P.root j) / 2) := by
    intro l
    rw [cartanBlock_apply, P.root'_coroot_eq_pairing, rootForm_root_root]
  have hsum : P.RootForm (∑ l : Θ, (cartanBlock P Θ)⁻¹ i l • P.root l) (P.root j) =
      ((cartanBlock P Θ)⁻¹ * cartanBlock P Θ) i j * (P.RootForm (P.root j) (P.root j) / 2) := by
    rw [map_sum, LinearMap.sum_apply, Matrix.mul_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_smul, LinearMap.smul_apply, smul_eq_mul, hkj, mul_assoc]
  rw [hsum, hinv, Matrix.one_apply]
  refine mul_nonneg ?_ (div_nonneg (rootForm_root_self_pos (P := P) (j : ι)).le zero_le_two)
  split_ifs <;> norm_num

omit [Fintype ι] [P.IsRootSystem] [P.IsCrystallographic] in
/-- Each weight is the combination of the simple roots of `Θ` with the coefficients of a row of
the inverse Cartan block (nonnegative by `cartanBlock_inv_nonneg`). -/
theorem weightCoordinate_eq_sum {Θ : Finset ι} {i : ι} (hi : i ∈ Θ) :
    weightCoordinate P Θ i = ∑ k : Θ, (cartanBlock P Θ)⁻¹ ⟨i, hi⟩ k • P.root' k := by
  simp only [weightCoordinate, hi, ↓reduceDIte]

end Langlands.ArthurCombinatorics
