import Langlands.Global.RankinSelberg.ComplexCompactDifferences
import Mathlib.Analysis.Calculus.MeanValue

/-! # Smooth matrix derivative bounds for compact right differences -/

noncomputable section

open Set
open scoped ContDiff Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexCompactSmoothDifferences

open Langlands.Archimedean (complexPositionCharacter complexStandardRep principalSeriesRep_apply_coe)
open Langlands.Archimedean.UnitaryFinitePolynomial (compactSpace_unitary)
open Langlands.LocalFactor.Archimedean (ComplexCharacterData)
open ComplexCompactDifferences (CompactDifferenceBound displacementProduct displacementProduct_nonneg
  iteratedDifference rightDifference)

local notation "Mat" => fun n => Matrix (Fin n) (Fin n) ℂ
local notation "K" => fun n => Matrix.unitaryGroup (Fin n) ℂ
local notation "Std" => Automorphic.complexStandardKFinite

variable {n : ℕ}

/-- The convex hull of the unitary group, in the real vector space of matrices. -/
def compactConvexHull (n : ℕ) : Set (Mat n) :=
  convexHull ℝ (Matrix.unitaryGroup (Fin n) ℂ : Set (Mat n))

private def rightMultiplication (k : K n) : Mat n →L[ℝ] Mat n :=
  (ContinuousLinearMap.mul ℝ (Mat n)).flip k.val

private theorem mapsTo_rightMultiplication (k : K n) :
    MapsTo (rightMultiplication k) (compactConvexHull n) (compactConvexHull n) := by
  intro x hx
  have h : (rightMultiplication k) '' compactConvexHull n ⊆ compactConvexHull n := by
    change (rightMultiplication k).toLinearMap '' compactConvexHull n ⊆ compactConvexHull n
    rw [compactConvexHull, LinearMap.image_convexHull]
    exact convexHull_mono (fun _ ⟨y, hy, he⟩ => he ▸ (Matrix.unitaryGroup (Fin n) ℂ).mul_mem hy k.2)
  exact h ⟨x, hx, rfl⟩

private theorem rightMultiplication_displacement (k : K n) (x : Mat n) :
    ‖rightMultiplication k x - x‖ ≤ ‖x‖ * ‖k.val - 1‖ := by
  change ‖x * k.val - x‖ ≤ _
  rw [show x * k.val - x = x * (k.val - 1) by rw [mul_sub, mul_one]]
  exact norm_mul_le _ _

private theorem norm_rightMultiplication_le {M : ℝ} (hM : 0 ≤ M) (k : K n) (hk : ‖k.val‖ ≤ M) :
    ‖rightMultiplication k‖ ≤ M :=
  ContinuousLinearMap.opNorm_le_bound _ hM fun x => (norm_mul_le x k.val).trans
    ((mul_le_mul_of_nonneg_left hk (norm_nonneg x)).trans_eq (mul_comm _ _))

private theorem norm_rightMultiplication_sub_id_le (k : K n) :
    ‖rightMultiplication k - ContinuousLinearMap.id ℝ (Mat n)‖ ≤ ‖k.val - 1‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x =>
    (rightMultiplication_displacement k x).trans_eq (mul_comm _ _)

/-- The ordinary iterated right difference of a function on the compact group. -/
def compactFunctionDifference (ks : List (K n)) (φ : K n → ℂ) : K n → ℂ :=
  ks.foldr (fun k g x => g (x * k) - g x) φ

/-- A uniform bound for compact function differences including the empty list. -/
def CompactProfileDifferenceBound (J : ℕ) (φ : K n → ℂ) (D : ℝ) : Prop :=
  ∀ (ks : List (K n)), ks.length ≤ J → ∀ x : K n,
    ‖compactFunctionDifference ks φ x‖ ≤ D * displacementProduct ks

theorem iteratedDifference_restriction {ds : List ComplexCharacterData} (ks : List (K n))
    (f : Std n ds) (k : K n) :
    (iteratedDifference ks f).val (Unitary.toUnits k) =
      compactFunctionDifference ks (fun x => f.val (Unitary.toUnits x)) k := by
  induction ks generalizing k with
  | nil => rfl
  | cons x xs ih =>
    change (complexStandardRep n ds x (iteratedDifference xs f)).val (Unitary.toUnits k) -
      (iteratedDifference xs f).val (Unitary.toUnits k) =
      compactFunctionDifference xs (fun u => f.val (Unitary.toUnits u)) (k * x) -
        compactFunctionDifference xs (fun u => f.val (Unitary.toUnits u)) k
    rw [show (complexStandardRep n ds x (iteratedDifference xs f)).val (Unitary.toUnits k) =
      (iteratedDifference xs f).val (Unitary.toUnits (k * x)) by
        rw [map_mul]
        exact congrFun (principalSeriesRep_apply_coe ℂ n (complexPositionCharacter ds) x
          (iteratedDifference xs f)) (Unitary.toUnits k), ih, ih]

theorem compactDifferenceBound_iff {ds : List ComplexCharacterData} (f : Std n ds) (J : ℕ) (D : ℝ) :
    CompactDifferenceBound J f D ↔
      CompactProfileDifferenceBound J (fun k => f.val (Unitary.toUnits k)) D := by
  constructor <;> intro h ks hks k
  · rw [← iteratedDifference_restriction]
    exact h ks hks k
  · rw [iteratedDifference_restriction]
    exact h ks hks k

private def matrixDifference (k : K n) (F : Mat n → ℂ) : Mat n → ℂ :=
  F ∘ rightMultiplication k - F

private def matrixDifferences (ks : List (K n)) (F : Mat n → ℂ) : Mat n → ℂ :=
  ks.foldr matrixDifference F

private theorem matrixDifferences_contDiff (ks : List (K n)) {F : Mat n → ℂ}
    (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (matrixDifferences ks F) := by
  induction ks with
  | nil => exact hF
  | cons k ks ih => exact (ih.comp (rightMultiplication k).contDiff).sub ih

private theorem matrixDifference_restriction (ks : List (K n)) (F : Mat n → ℂ) (k : K n) :
    matrixDifferences ks F k.val = compactFunctionDifference ks (fun x => F x.val) k := by
  induction ks generalizing k with
  | nil => rfl
  | cons x xs ih =>
    change matrixDifferences xs F (k * x : K n).val - matrixDifferences xs F k.val = _
    exact congrArg₂ Sub.sub (ih (k * x)) (ih k)

/-- A simultaneous bound for the real matrix derivatives of orders at most `J`
on the compact convex hull of the unitary group. -/
def CompactMatrixJetBound (J : ℕ) (F : Mat n → ℂ) (D : ℝ) : Prop :=
  ∀ (i : ℕ), i ≤ J → ∀ x ∈ compactConvexHull n, ‖iteratedFDeriv ℝ i F x‖ ≤ D

private theorem variation_of_multilinear_arguments (j : ℕ)
    (Q : ContinuousMultilinearMap ℝ (fun _ : Fin j => Mat n) ℂ) (k : K n) {M : ℝ}
    (hM : 1 ≤ M) (hk : ‖k.val‖ ≤ M) :
    ‖Q.compContinuousLinearMap (fun _ => rightMultiplication k) - Q‖ ≤
      ‖Q‖ * j * M ^ j * ‖k.val - 1‖ := by
  let A := rightMultiplication k
  let I := ContinuousLinearMap.id ℝ (Mat n)
  let a : Fin j → Mat n →L[ℝ] Mat n := fun _ => A
  let b : Fin j → Mat n →L[ℝ] Mat n := fun _ => I
  let P := Q.compContinuousLinearMapLRight (E := fun _ : Fin j => Mat n)
  have hA : ‖A‖ ≤ M := norm_rightMultiplication_le (zero_le_one.trans hM) k hk
  have hI : ‖I‖ ≤ M := ContinuousLinearMap.norm_id_le.trans hM
  have hb : P b = Q := by
    ext m
    rfl
  have hs : ‖a - b‖ ≤ ‖k.val - 1‖ :=
    (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun _ => norm_rightMultiplication_sub_id_le k
  have hmax : max ‖a‖ ‖b‖ ≤ M := max_le (pi_norm_const_le _ |>.trans hA) (pi_norm_const_le _ |>.trans hI)
  have hpow : (max ‖a‖ ‖b‖) ^ (j - 1) ≤ M ^ j :=
    (pow_le_pow_left₀ ((norm_nonneg a).trans (le_max_left _ _)) hmax _).trans
      (pow_le_pow_right₀ hM (Nat.sub_le _ _))
  change ‖P a - Q‖ ≤ _
  calc
    _ = ‖P a - P b‖ := by rw [hb]
    _ ≤ ‖P‖ * (j : ℝ) * (max ‖a‖ ‖b‖) ^ (j - 1) * ‖a - b‖ := by
      simpa only [Fintype.card_fin] using P.norm_image_sub_le a b
    _ ≤ _ := by
      gcongr
      exact Q.norm_compContinuousLinearMapLRight_le _

/-- The derivative of one right difference is bounded on a convex set containing both
base points. The single move contributes one factor of its matrix displacement. -/
theorem matrixDifference_jet_bound_on {S : Set (Mat n)} (hS : Convex ℝ S)
    {F : Mat n → ℂ} (hF : ContDiff ℝ ∞ F) {j : ℕ} {M D : ℝ} (hM : 1 ≤ M) (hD : 0 ≤ D)
    (hjet : ∀ i ≤ j + 1, ∀ y ∈ S, ‖iteratedFDeriv ℝ i F y‖ ≤ D)
    (k : K n) (hk : ‖k.val‖ ≤ M) {x : Mat n} (hx : x ∈ S) (hAx : x * k.val ∈ S)
    (hxnorm : ‖x‖ ≤ M) :
    ‖iteratedFDeriv ℝ j (fun y => F (y * k.val) - F y) x‖ ≤ M ^ j * (M + j) * D * ‖k.val - 1‖ := by
  let A := rightMultiplication k
  have hjlt : (j : WithTop ℕ∞) < ∞ := WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top j)
  have hDiff : ‖iteratedFDeriv ℝ j F (A x) - iteratedFDeriv ℝ j F x‖ ≤ D * (M * ‖k.val - 1‖) := by
    have hLip := hS.norm_image_sub_le_of_norm_fderiv_le
      (f := iteratedFDeriv ℝ j F) (C := D)
      (fun _ _ => (hF.differentiable_iteratedFDeriv hjlt).differentiableAt)
      (fun y hy => by rw [norm_fderiv_iteratedFDeriv]; exact hjet _ le_rfl y hy)
      hx hAx
    exact hLip.trans (mul_le_mul_of_nonneg_left ((rightMultiplication_displacement k x).trans
      (mul_le_mul_of_nonneg_right hxnorm (norm_nonneg _))) hD)
  have hCompose : ‖A‖ ≤ M := norm_rightMultiplication_le (zero_le_one.trans hM) k hk
  have hFirst : ‖(iteratedFDeriv ℝ j F (A x) - iteratedFDeriv ℝ j F x).compContinuousLinearMap
      (fun _ => A)‖ ≤ D * (M * ‖k.val - 1‖) * M ^ j := by
    apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact mul_le_mul hDiff (pow_le_pow_left₀ (norm_nonneg A) hCompose _) (by positivity) (by positivity)
  have hSecond := variation_of_multilinear_arguments j (iteratedFDeriv ℝ j F x) k hM hk
  change ‖iteratedFDeriv ℝ j (F ∘ A - F) x‖ ≤ _
  rw [iteratedFDeriv_sub_apply ((hF.comp A.contDiff).of_le hjlt.le).contDiffAt
    (hF.of_le hjlt.le).contDiffAt, A.iteratedFDeriv_comp_right hF x hjlt.le]
  let S := ContinuousMultilinearMap.compContinuousLinearMapL (F := ℂ) (fun _ : Fin j => A)
  let X := iteratedFDeriv ℝ j F (A x)
  let Y := iteratedFDeriv ℝ j F x
  change ‖S X - Y‖ ≤ _
  rw [show S X - Y = S (X - Y) + (S Y - Y) by rw [map_sub]; abel]
  calc
    _ ≤ ‖S (X - Y)‖ + ‖S Y - Y‖ := norm_add_le _ _
    _ ≤ D * (M * ‖k.val - 1‖) * M ^ j + D * j * M ^ j * ‖k.val - 1‖ := by
      apply add_le_add hFirst (hSecond.trans _)
      gcongr
      exact hjet j (Nat.le_succ _) x hx
    _ = _ := by ring

private theorem matrixDifference_jet_bound {F : Mat n → ℂ} (hF : ContDiff ℝ ∞ F)
    {j : ℕ} {M D : ℝ} (hM : 1 ≤ M) (hD : 0 ≤ D)
    (hQ : ∀ x ∈ compactConvexHull n, ‖x‖ ≤ M) (h : CompactMatrixJetBound (j + 1) F D)
    (k : K n) {x : Mat n} (hx : x ∈ compactConvexHull n) :
    ‖iteratedFDeriv ℝ j (matrixDifference k F) x‖ ≤ M ^ j * (M + j) * D * ‖k.val - 1‖ :=
  matrixDifference_jet_bound_on (convex_convexHull ℝ _) hF hM hD h k
    (hQ k.val (subset_convexHull ℝ _ k.2)) hx (mapsTo_rightMultiplication k hx) (hQ x hx)

/-- Finite differences on unitary matrices are controlled by finitely many
real derivatives of a smooth extension to the matrix space. -/
def ComplexCompactSmoothDifferencesStatement : Prop :=
  ∀ (n J : ℕ), ∃ C : ℝ, 1 ≤ C ∧ ∀ (F : Mat n → ℂ) (D : ℝ),
    ContDiff ℝ ∞ F → 0 ≤ D → CompactMatrixJetBound J F D →
      CompactProfileDifferenceBound J (fun k => F k.val) (C * D)

set_option maxHeartbeats 700000 in
theorem complexCompactSmoothDifferences : ComplexCompactSmoothDifferencesStatement := by
  intro n J
  let : CompactSpace (K n) := compactSpace_unitary n
  obtain ⟨B, hB⟩ := (isCompact_range (continuous_subtype_val.norm :
    Continuous (fun k : K n => ‖k.val‖))).bddAbove
  let M := max 1 B
  have hM : 1 ≤ M := le_max_left _ _
  have hQ : ∀ x ∈ compactConvexHull n, ‖x‖ ≤ M := by
    have hball : compactConvexHull n ⊆ Metric.closedBall 0 M :=
      convexHull_min (fun x hx => mem_closedBall_zero_iff.mpr
        ((hB (mem_range_self (⟨x, hx⟩ : K n))).trans (le_max_right _ _)))
        (convex_closedBall _ _)
    exact fun x hx => mem_closedBall_zero_iff.mp (hball hx)
  let L := M ^ J * (M + J)
  have hL : 1 ≤ L := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hM)
    (hM.trans (le_add_of_nonneg_right (Nat.cast_nonneg J)))
  refine ⟨L ^ J, one_le_pow₀ hL, fun F D hF hD hFJ ks hks k => ?_⟩
  have bound (zs : List (K n)) (i : ℕ) (hi : i + zs.length ≤ J) :
      CompactMatrixJetBound i (matrixDifferences zs F) (L ^ zs.length * D * displacementProduct zs) := by
    induction zs generalizing i with
    | nil =>
      intro j hj x hx
      simpa [matrixDifferences, displacementProduct] using hFJ j (hj.trans hi) x hx
    | cons z zs ih =>
      have hd := ih (i + 1) (by simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm 1 zs.length] using hi)
      intro j hj x hx
      have hd' : CompactMatrixJetBound (j + 1) (matrixDifferences zs F)
          (L ^ zs.length * D * displacementProduct zs) := fun t ht => hd t (ht.trans (Nat.succ_le_succ hj))
      have hn : 0 ≤ L ^ zs.length * D * displacementProduct zs :=
        mul_nonneg (mul_nonneg (pow_nonneg (zero_le_one.trans hL) _) hD) (displacementProduct_nonneg zs)
      have hstep := matrixDifference_jet_bound (matrixDifferences_contDiff zs hF) hM hn hQ hd' z hx
      refine hstep.trans ?_
      have hcoef : M ^ j * (M + j) ≤ L := by
        have hle : j ≤ J := hj.trans (Nat.le_trans (Nat.le_add_right _ _) hi)
        dsimp only [L]
        exact mul_le_mul (pow_le_pow_right₀ hM hle) (add_le_add le_rfl (Nat.cast_le.mpr hle))
          (by positivity) (by positivity)
      calc
        _ ≤ L * (L ^ zs.length * D * displacementProduct zs) * ‖z.val - 1‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef hn) (norm_nonneg _)
        _ = L ^ (z :: zs).length * D * displacementProduct (z :: zs) := by
          simp only [List.length_cons, displacementProduct, List.map_cons, List.prod_cons, pow_succ]
          ring
  have h := bound ks 0 (by simpa only [Nat.zero_add] using hks) 0 le_rfl k.val (subset_convexHull ℝ _ k.2)
  rw [norm_iteratedFDeriv_zero, matrixDifference_restriction] at h
  exact h.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hL hks) hD)
    (displacementProduct_nonneg ks))

end Langlands.Global.RankinSelbergGlobal.ComplexCompactSmoothDifferences
