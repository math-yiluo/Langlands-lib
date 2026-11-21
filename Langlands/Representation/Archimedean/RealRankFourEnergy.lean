import Langlands.Representation.Archimedean.RealRankFourMatrices
import Langlands.Representation.Archimedean.RealRankFourNormComparison

/-!
# The rank-four energy inequality

The three spin-one column estimates are compared with the trace-free Casimir
on a highest vector of the left compact triple fixed by the right triple.
-/

noncomputable section

set_option autoImplicit false

namespace Langlands.Archimedean.RealRankFourEnergy

open Complex RealRankFourMatrices RealRankFourNormComparison
open scoped InnerProductSpace BigOperators

attribute [local instance 100] LieRing.ofAssociativeRing

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

variable (A : MatC →ₗ⁅ℂ⁆ Module.End ℂ V)

private theorem apply_lie (X Y : MatC) (v : V) :
    A ⁅X, Y⁆ v = A X (A Y v) - A Y (A X v) := by
  rw [A.map_lie, LieRing.of_associative_ring_bracket]
  rfl

private theorem swap_actions (X Y : MatC) (v : V) :
    A X (A Y v) = A ⁅X, Y⁆ v + A Y (A X v) :=
  (eq_sub_iff_add_eq.mp (apply_lie A X Y v)).symm

variable (hskew : ∀ (b : Fin 4 × Fin 4) (x y : V),
  ⟪A (basisC b) x, y⟫_ℂ = -⟪x, A (basisC b) y⟫_ℂ)

include hskew in
private theorem lowering_adjoint (x y : V) :
    ⟪A lowering x, y⟫_ℂ = ⟪x, A raising y⟫_ℂ := by
  simp only [lowering, raising, map_sub, map_neg, map_smul, LinearMap.sub_apply,
    LinearMap.neg_apply, LinearMap.smul_apply, inner_sub_left, inner_neg_left,
    inner_smul_left, inner_sub_right, inner_smul_right, hskew]
  change -(-⟪x, A (K 0) y⟫_ℂ) - star I * (-⟪x, A (K 1) y⟫_ℂ) =
    ⟪x, A (K 0) y⟫_ℂ - I * ⟪x, A (K 1) y⟫_ℂ
  rw [show star I = -I from Complex.conj_I]
  ring

include hskew in
private theorem column_ge (weight : ℝ) (hweight : 0 < weight) (v : V)
    (hvE : A raising v = 0) (hvH : A cartan v = (weight : ℂ) • v) (j : Fin 3) :
    (weight / 2 + 1) * ‖v‖ ^ 2 ≤ ∑ i : Fin 3, ‖A (P i j) v‖ ^ 2 := by
  let u := A (upperColumn j) v
  let w := A (lowerColumn j) v
  let y := A (P 2 j) v
  have hEu : A raising u = 0 := by
    dsimp only [u]
    rw [swap_actions A raising, raising_lie_upperColumn, hvE, map_zero,
      LinearMap.zero_apply, map_zero, add_zero]
  have hHu : A cartan u = ((weight + 2 : ℝ) : ℂ) • u := by
    dsimp only [u]
    rw [swap_actions A cartan, cartan_lie_upperColumn, hvH]
    simp only [map_smul, LinearMap.smul_apply]
    push_cast
    module
  have hFu : A raising (A lowering u) = ((weight + 2 : ℝ) : ℂ) • u := by
    rw [swap_actions A raising, raising_lie_lowering, hHu, hEu, map_zero, add_zero]
  have hHFu : A cartan (A lowering u) = (weight : ℂ) • A lowering u := by
    rw [swap_actions A cartan, cartan_lie_lowering, hHu]
    simp only [map_smul, LinearMap.smul_apply]
    push_cast
    module
  have hFFu : A raising (A lowering (A lowering u)) =
      ((2 * (weight + 1) : ℝ) : ℂ) • A lowering u := by
    rw [swap_actions A raising, raising_lie_lowering, hHFu, hFu, map_smul]
    push_cast
    module
  have hEy : A raising y = -I • u := by
    dsimp only [y]
    rw [swap_actions A raising, raising_lie_middleColumn, hvE, map_zero, add_zero]
    simp only [map_smul, LinearMap.smul_apply, u]
  have hEw : A raising w = (2 * I) • y := by
    dsimp only [w]
    rw [swap_actions A raising, raising_lie_lowerColumn, hvE, map_zero, add_zero]
    simp only [map_smul, LinearMap.smul_apply, y]
  have hEEw : A raising (A raising w) = (2 : ℂ) • u := by
    rw [hEw, map_smul, hEy, smul_smul]
    congr 1
    rw [mul_assoc, mul_neg, I_mul_I, neg_neg, mul_one]
  have hdiff : ‖u‖ ^ 2 - ‖w‖ ^ 2 = weight * ‖v‖ ^ 2 := by
    have h := apply_lie A (upperColumn j) (lowerColumn j) v
    rw [upperColumn_lie_lowerColumn, hvH] at h
    simp only [u, w, upperColumn, lowerColumn, map_sub, map_add, map_smul]
    apply normSq_sub_normSq_of_commutator v (A (P 0 j)) (A (P 1 j)) weight
      (hskew ((0 : Fin 3).succ, j.succ)) (hskew ((1 : Fin 3).succ, j.succ))
    simpa only [upperColumn, lowerColumn, map_sub, map_add, map_smul,
      LinearMap.sub_apply, Module.End.mul_apply] using h.symm
  have hpara := parallelogram_law_with_norm ℂ (A (P 0 j) v) (I • A (P 1 j) v)
  have hu : u = A (P 0 j) v - I • A (P 1 j) v := by simp [u, upperColumn]
  have hw : w = A (P 0 j) v + I • A (P 1 j) v := by simp [w, lowerColumn]
  rw [← hu, ← hw, norm_smul, norm_I, one_mul] at hpara
  have h := columnEnergy_ge hweight v u w y (A raising) (A lowering)
    (lowering_adjoint A hskew) hFu hFFu hEy hEEw hdiff
  rw [Fin.sum_univ_three]
  dsimp only [y] at h
  linarith only [h, hpara]

private theorem compact_square_sum (m : ℝ) (v : V) (hvE : A raising v = 0)
    (hvK : A (K 2) v = ((m : ℂ) * I) • v) :
    (∑ i : Fin 3, A (K i) ^ 2) v = ((-m * (m + 1) : ℝ) : ℂ) • v := by
  have h0 : A (K 0) v = I • A (K 1) v :=
    sub_eq_zero.mp (by simpa only [raising, map_sub, map_smul, LinearMap.sub_apply,
      LinearMap.smul_apply] using hvE)
  have h01 : A (K 0) (A (K 0) v) + A (K 1) (A (K 1) v) = I • A (K 2) v := by
    calc
      _ = I • A (K 0) (A (K 1) v) + A (K 1) (A (K 1) v) := by rw [← map_smul, ← h0]
      _ = _ := by
        rw [swap_actions A (K 0), left_lie.1, h0, map_smul, smul_add,
          smul_smul, I_mul_I, neg_one_smul, neg_add_cancel_right]
  have h2 : A (K 2) (A (K 2) v) = (((m : ℂ) * I) * ((m : ℂ) * I)) • v := by
    conv_lhs => rw [hvK]
    rw [map_smul, hvK, smul_smul]
  rw [Fin.sum_univ_three, LinearMap.add_apply, LinearMap.add_apply]
  simp only [pow_two, Module.End.mul_apply]
  rw [h01, h2, hvK, smul_smul]
  push_cast
  match_scalars
  ring_nf
  simp [pow_two, I_mul_I]
  ring

include hskew in
/-- A highest vector of compact spins `(m, 0)` with the indicated trace-free
Casimir eigenvalue gives the weak bound on the real opposite twist. -/
theorem abs_le_half (m a : ℝ) (hm : 0 < m) (v : V) (hv : v ≠ 0)
    (hvE : A raising v = 0) (hvK : A (K 2) v = ((m : ℂ) * I) • v)
    (hvR : ∀ j : Fin 3, A (R j) v = 0)
    (hcas : ((∑ p : Fin 4, ∑ q : Fin 4, A (Matrix.single p q 1) * A (Matrix.single q p 1)) -
      A (basisC (0, 0)) ^ 2) v = (((m - 1) ^ 2 + 4 * a ^ 2 - 5 : ℝ) : ℂ) • v) :
    |a| ≤ 1 / 2 := by
  have hvH : A cartan v = ((2 * m : ℝ) : ℂ) • v := by
    simp only [cartan, map_smul, LinearMap.smul_apply, hvK, smul_smul]
    push_cast
    match_scalars
    ring_nf
    simp [pow_two, I_mul_I]
  have hle := Finset.sum_le_sum (fun (j : Fin 3) (_ : j ∈ Finset.univ) =>
    column_ge A hskew (2 * m) (by positivity) v hvE hvH j)
  rw [Finset.sum_comm (f := fun j i => ‖A (P i j) v‖ ^ 2)] at hle
  have hR : (∑ j : Fin 3, A (R j) ^ 2) v = 0 := by
    simp only [LinearMap.sum_apply, pow_two, Module.End.mul_apply, hvR, map_zero, Finset.sum_const_zero]
  change ((∑ p : Fin 4, ∑ q : Fin 4, A.toLinearMap (Matrix.single p q 1) *
    A.toLinearMap (Matrix.single q p 1)) - A.toLinearMap (basisC (0, 0)) ^ 2) v = _ at hcas
  rw [casimir_split A.toLinearMap, add_sub_cancel_right] at hcas
  simp only [LieHom.coe_toLinearMap, LinearMap.sub_apply, compact_square_sum A m v hvE hvK,
    hR, sub_zero] at hcas
  have hP : (∑ i : Fin 3, ∑ j : Fin 3, A (P i j) ^ 2) v =
      ((4 * a ^ 2 - 3 * m - 4 : ℝ) : ℂ) • v := by
    rw [sub_eq_iff_eq_add] at hcas
    rw [hcas]
    push_cast
    module
  have hinner := congrArg (fun z : V => Complex.reCLM ⟪v, z⟫_ℂ) hP
  have hs (i j : Fin 3) : ⟪v, A (P i j) (A (P i j) v)⟫_ℂ =
      -⟪A (P i j) v, A (P i j) v⟫_ℂ := by
    rw [hskew (i.succ, j.succ) v (A (P i j) v), neg_neg]
  have hre (x : V) : (⟪x, x⟫_ℂ).re = ‖x‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) x
  simp only [LinearMap.sum_apply, pow_two, Module.End.mul_apply] at hinner
  simp only [inner_sum, hs, map_sum, map_neg, reCLM_apply, hre, inner_smul_right, mul_re, ofReal_re,
    ofReal_im, zero_mul, sub_zero, Finset.sum_neg_distrib] at hinner
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_ofNat] at hle
  have hle' : (3 * (m + 1)) * ‖v‖ ^ 2 ≤ (3 * m + 4 - 4 * a ^ 2) * ‖v‖ ^ 2 := by
    linarith only [hle, hinner]
  have hnum := (mul_le_mul_iff_left₀ (sq_pos_of_pos (norm_pos_iff.mpr hv))).mp hle'
  exact abs_le_of_sq_le_sq (by nlinarith only [hnum]) (by positivity)

end Langlands.Archimedean.RealRankFourEnergy
