import Langlands.LinearAlgebra.ArthurCombinatoricsSigma

/-! # Simple-root bounds on the truncated support of Arthur's sigma function -/

noncomputable section
set_option autoImplicit false

namespace Langlands.ArthurCombinatorics

open Finset

variable {I M N : Type*} [DecidableEq I] [Finite I] [AddCommGroup M] [Module ℝ M]
  [AddCommGroup N] [Module ℝ N] {P : RootPairing I ℝ M N} [P.IsRootSystem]
  [P.IsCrystallographic] (b : P.Base)

/-- On the support of `σ_{R}^{S}`, suppose the roots in `R` are bounded below
and the coefficients on the `R`-coroots are nonpositive. The active roots
in `S \ R` are then positive. An upper bound on them gives an absolute bound
on every simple root, linear in the two supplied bounds. -/
def ArthurSigmaRootBoundsStatement (R S : Finset I) : Prop :=
  R ⊆ S → S ⊆ b.support → ∃ C : ℝ, 0 ≤ C ∧ ∀ Z : N, ∀ B₁ B₂ : ℝ, 0 ≤ B₁ → 0 ≤ B₂ →
    (∀ j ∈ R, -B₁ ≤ P.root' j Z) →
    (∀ j ∈ R, weightCoordinate P R j Z ≤ 0) →
    sigma P b.support R S Z = 1 →
    (∀ j ∈ S \ R, P.root' j Z ≤ B₂) →
    (∀ j ∈ S \ R, 0 < P.root' j Z) ∧
      ∀ j ∈ b.support, |P.root' j Z| ≤ C * (B₁ + B₂)

theorem arthurSigmaRootBounds (R S : Finset I) : ArthurSigmaRootBoundsStatement b R S := by
  classical
  intro hRS hS
  let hR := hRS.trans hS
  let D := b.support
  let W := (cartanBlock P D)⁻¹
  let W₁ := (cartanBlock P R)⁻¹
  let K := ∑ i : D, ∑ j : D, W i j
  let K₁ := ∑ i : R, ∑ j : R, W₁ i j
  let L := ∑ i : D, ∑ j : R, |P.root' i (P.coroot j)|
  have hW (i j : D) : 0 ≤ W i j := cartanBlock_inv_nonneg' b subset_rfl i j
  have hW₁ (i j : R) : 0 ≤ W₁ i j := cartanBlock_inv_nonneg' b hR i j
  have hK : 0 ≤ K := sum_nonneg fun i _ => sum_nonneg fun j _ => hW i j
  have hK₁ : 0 ≤ K₁ := sum_nonneg fun i _ => sum_nonneg fun j _ => hW₁ i j
  have hL : 0 ≤ L := sum_nonneg fun i _ => sum_nonneg fun j _ => abs_nonneg _
  have hrow (i : D) : (∑ j : D, W i j) ≤ K :=
    single_le_sum (fun i _ => sum_nonneg fun j _ => hW i j) (mem_univ i)
  have hrow₁ (i : R) : (∑ j : R, W₁ i j) ≤ K₁ :=
    single_le_sum (fun i _ => sum_nonneg fun j _ => hW₁ i j) (mem_univ i)
  have hrowL (i : D) : (∑ j : R, |P.root' i (P.coroot j)|) ≤ L :=
    single_le_sum (f := fun i : D => ∑ j : R, |P.root' i (P.coroot j)|)
      (fun _ _ => sum_nonneg fun _ _ => abs_nonneg _) (mem_univ i)
  refine ⟨1 + 2 * K + L * K₁, by positivity, fun Z B₁ B₂ hB₁ hB₂ hlo hwt hσ hhi => ?_⟩
  let Y := levelProjection P R Z
  let X := ∑ j : R, weightCoordinate P R j Z • P.coroot j
  have hZ : Y + X = Z := by
    rw [show Y = Z - X from levelProjection_apply (P := P) R Z, sub_add_cancel]
  have hXapply (i : I) : P.root' i X =
      ∑ j : R, weightCoordinate P R j Z * P.root' i (P.coroot j) := by
    simp [X, map_sum, map_smul, smul_eq_mul]
  have hXpos {i : I} (hi : i ∈ D) (hiR : i ∉ R) : 0 ≤ P.root' i X := by
    rw [hXapply]
    refine sum_nonneg fun j _ => mul_nonneg_of_nonpos_of_nonpos (hwt j j.2) ?_
    let : Fintype I := Fintype.ofFinite I
    rw [P.root'_coroot_eq_pairing]
    exact pairing_nonpos_of_ne b (fun e => hiR (e.symm ▸ j.2)) hi (hR j.2)
  have hXbound (i : D) : |P.root' i X| ≤ L * K₁ * B₁ := by
    have hweight (j : R) : |weightCoordinate P R j Z| ≤ K₁ * B₁ := by
      have hsum : (∑ k : R, W₁ j k * -B₁) ≤ weightCoordinate P R j Z := by
        rw [weightCoordinate_apply j.2]
        exact sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hlo k k.2) (hW₁ j k)
      rw [← sum_mul, mul_neg] at hsum
      rw [abs_of_nonpos (hwt j j.2)]
      linarith [mul_le_mul_of_nonneg_right (hrow₁ j) hB₁]
    rw [hXapply]
    calc
      _ ≤ ∑ j : R, |weightCoordinate P R j Z * P.root' i (P.coroot j)| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ j : R, |P.root' i (P.coroot j)| * (K₁ * B₁) := by
        refine sum_le_sum fun j _ => ?_
        rw [abs_mul, mul_comm]
        exact mul_le_mul_of_nonneg_left (hweight j) (abs_nonneg _)
      _ ≤ L * K₁ * B₁ := by
        rw [← sum_mul, mul_assoc]
        exact mul_le_mul_of_nonneg_right (hrowL i) (mul_nonneg hK₁ hB₁)
  have hSigma : (∀ i ∈ S \ R, 0 < P.root' i Y) ∧ (∀ i ∈ D \ S, P.root' i Y ≤ 0) ∧
      (∀ i ∈ D \ S, 0 < weightCoordinate P D i Z) := by
    by_contra hn
    rw [sigma_eq hRS hS subset_rfl, ite_eq_right hn] at hσ
    exact zero_ne_one hσ
  obtain ⟨hactive, houtside, hweights⟩ := hSigma
  have hrootZ (i : I) : P.root' i Y + P.root' i X = P.root' i Z := by rw [← map_add, hZ]
  have hPos (i : I) (hi : i ∈ S \ R) : 0 < P.root' i Z := by
    have hX := hXpos (hS (mem_sdiff.mp hi).1) (mem_sdiff.mp hi).2
    linarith [hactive i hi, hrootZ i]
  have hYupper (i : D) : P.root' i Y ≤ B₂ := by
    by_cases hiR : (i : I) ∈ R
    · rw [root'_levelProjection_eq_zero b hR Z hiR]
      exact hB₂
    · by_cases hiS : (i : I) ∈ S
      · have hi : (i : I) ∈ S \ R := mem_sdiff.mpr ⟨hiS, hiR⟩
        linarith [hhi i hi, hXpos i.2 hiR, hrootZ i]
      · exact (houtside i (mem_sdiff.mpr ⟨i.2, hiS⟩)).trans hB₂
  have hYlower (i : D) : -(2 * K * B₂) ≤ P.root' i Y := by
    by_cases hiS : (i : I) ∈ S
    · have hz : 0 ≤ P.root' i Y := by
        by_cases hiR : (i : I) ∈ R
        · rw [root'_levelProjection_eq_zero b hR Z hiR]
        · exact (hactive i (mem_sdiff.mpr ⟨hiS, hiR⟩)).le
      exact (neg_nonpos.mpr (by positivity)).trans hz
    · have hi : (i : I) ∈ D \ S := mem_sdiff.mpr ⟨i.2, hiS⟩
      have hiR : (i : I) ∉ R := fun h => hiS (hRS h)
      have hcoord := hweights i hi
      rw [← weightCoordinate_levelProjection b hR subset_rfl i.2 hiR Z,
        weightCoordinate_apply i.2] at hcoord
      change 0 < ∑ j : D, W i j * P.root' j Y at hcoord
      have hterm (j : D) : 0 ≤ W i j * (B₂ - P.root' j Y) :=
        mul_nonneg (hW i j) (sub_nonneg.mpr (hYupper j))
      have hdiag := single_le_sum (fun j _ => hterm j) (mem_univ i)
      have hdiag' : (B₂ - P.root' i Y) / 2 ≤ W i i * (B₂ - P.root' i Y) := by
        have hh := mul_le_mul_of_nonneg_right (half_le_cartanBlock_inv_self b subset_rfl i)
          (sub_nonneg.mpr (hYupper i))
        linarith
      have hsplit : (∑ j : D, W i j * (B₂ - P.root' j Y)) =
          (∑ j : D, W i j) * B₂ - ∑ j : D, W i j * P.root' j Y := by
        simp_rw [mul_sub, sum_sub_distrib, sum_mul]
      linarith [hdiag, hdiag', hsplit, mul_le_mul_of_nonneg_right (hrow i) hB₂]
  refine ⟨hPos, fun i hi => ?_⟩
  have hY : |P.root' i Y| ≤ (1 + 2 * K) * B₂ := by
    rw [abs_le]
    have h₁ : 0 ≤ 2 * K * B₂ := by positivity
    constructor <;> linarith [hYlower ⟨i, hi⟩, hYupper ⟨i, hi⟩]
  calc
    |P.root' i Z| = |P.root' i Y + P.root' i X| := by rw [hrootZ]
    _ ≤ |P.root' i Y| + |P.root' i X| := abs_add_le _ _
    _ ≤ (1 + 2 * K) * B₂ + L * K₁ * B₁ := add_le_add hY (hXbound ⟨i, hi⟩)
    _ ≤ (1 + 2 * K + L * K₁) * (B₁ + B₂) := by
      have h₁ : 0 ≤ (1 + 2 * K) * B₁ := by positivity
      have h₂ : 0 ≤ L * K₁ * B₂ := by positivity
      nlinarith

end Langlands.ArthurCombinatorics
