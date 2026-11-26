import Langlands.Global.RankinSelberg.RealRankRaisingIntegral
import Langlands.Geometry.Manifold.LinearLieGroup.ClosedSubgroup

/-! # The closed subgroup for real rank raising -/

noncomputable section

open Matrix Set
open scoped Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealRankRaisingIntegral

open Langlands.GeneralLinear Langlands.LinearLieGroup
open Langlands.GeneralLinear.Iwasawa (diagonalUnits_val)

local notation "G" => fun r => Langlands.GeneralLinear (r + 1) ℝ
local notation "B" => lowerTriangularSubgroup 1 ℝ
local notation "X" => fun r => Matrix (Fin 1) (Fin (r + 1)) ℝ
local notation "P" => fun r => X r × B

private def blocks {r : ℕ} (g : G (r + 1)) :
    Matrix (Fin (r + 1) ⊕ Fin 1) (Fin (r + 1) ⊕ Fin 1) ℝ :=
  g.val.submatrix finSumFinEquiv finSumFinEquiv

private theorem blocks_injective {r : ℕ} : Function.Injective (blocks (r := r)) := by
  intro g g' h
  apply Units.ext
  ext i j
  simpa only [blocks, Matrix.submatrix_apply, Equiv.apply_symm_apply] using
    congrFun (congrFun h (finSumFinEquiv.symm i)) (finSumFinEquiv.symm j)

private theorem blocks_smoothingMatrix {r : ℕ} (y : P r) :
    blocks (rankRaisingSmoothingMatrix y) =
      Matrix.fromBlocks (rankRaisingDiagonal r y.2)⁻¹.val 0 y.1 y.2.val.val :=
  lowerBlockPair_val_submatrix _ _ _

theorem rankRaisingDiagonal_mul (r : ℕ) (h k : B) :
    rankRaisingDiagonal r (h * k) = rankRaisingDiagonal r h * rankRaisingDiagonal r k := by
  apply Units.ext
  simp only [rankRaisingDiagonal, diagonalUnits_val, Units.val_mul, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  by_cases hi : i = 0 <;> simp [hi]

private theorem rankRaisingDiagonal_one (r : ℕ) : rankRaisingDiagonal r (1 : B) = 1 := by
  apply Units.ext
  simp only [rankRaisingDiagonal, Subgroup.coe_one, map_one, ite_self, diagonalUnits_val,
    Units.val_one, Matrix.diagonal_one]

theorem rankRaisingSmoothingMatrix_mul {r : ℕ} (u v : P r) :
    rankRaisingSmoothingMatrix u * rankRaisingSmoothingMatrix v =
      rankRaisingSmoothingMatrix
        (u.1 * (rankRaisingDiagonal r v.2)⁻¹.val + u.2.val.val * v.1, u.2 * v.2) := by
  have hc : rankRaisingDiagonal r (u.2 * v.2) = rankRaisingDiagonal r (v.2 * u.2) := by
    unfold rankRaisingDiagonal
    simp only [Subgroup.coe_mul, map_mul, mul_comm (determinant u.2.val)]
  have he : (rankRaisingDiagonal r u.2)⁻¹ * (rankRaisingDiagonal r v.2)⁻¹ =
      (rankRaisingDiagonal r (u.2 * v.2))⁻¹ := by
    rw [hc, rankRaisingDiagonal_mul, _root_.mul_inv_rev]
  simp only [rankRaisingSmoothingMatrix, lowerBlockPair_mul_lowerBlockPair, he]

private theorem smoothingMatrix_inv {r : ℕ} (u : P r) :
    (rankRaisingSmoothingMatrix u)⁻¹ =
      rankRaisingSmoothingMatrix
        (-(u.2⁻¹ : B).val.val * u.1 * (rankRaisingDiagonal r u.2).val, u.2⁻¹) := by
  have he : rankRaisingDiagonal r (u.2⁻¹ : B) = (rankRaisingDiagonal r u.2)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← rankRaisingDiagonal_mul, inv_mul_cancel, rankRaisingDiagonal_one]
  simp only [rankRaisingSmoothingMatrix, lowerBlockPair_inv, he, inv_inv, Subgroup.coe_inv]

/-- The subgroup of matrices `[a(h)⁻¹,0;x,h]` with one trailing coordinate. -/
def rankRaisingSubgroup (r : ℕ) : Subgroup (G (r + 1)) where
  carrier := range (rankRaisingSmoothingMatrix (r := r))
  one_mem' := by
    refine ⟨(0, 1), blocks_injective ?_⟩
    rw [blocks_smoothingMatrix]
    simp only [rankRaisingDiagonal_one, inv_one, Units.val_one, Subgroup.coe_one, blocks]
    rw [Matrix.submatrix_one_equiv]
    exact Matrix.fromBlocks_one
  mul_mem' := by
    rintro _ _ ⟨u, rfl⟩ ⟨v, rfl⟩
    exact ⟨_, (rankRaisingSmoothingMatrix_mul u v).symm⟩
  inv_mem' := by
    rintro _ ⟨u, rfl⟩
    exact ⟨_, (smoothingMatrix_inv u).symm⟩

private def tailEntry {r : ℕ} (g : G (r + 1)) : ℝ := (blocks g).toBlocks₂₂ 0 0

private def entryDiagonal (r : ℕ) (h : ℝ) : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ :=
  Matrix.diagonal (fun i => if i = 0 then h else 1)

private theorem rankRaisingDiagonal_val (r : ℕ) (h : B) :
    (rankRaisingDiagonal r h).val = entryDiagonal r (h.val.val 0 0) := by
  rw [rankRaisingDiagonal, diagonalUnits_val, entryDiagonal]
  congr 1
  funext i
  by_cases hi : i = 0
  · simp only [hi, ite_true]
    exact Matrix.det_fin_one _
  · simp only [hi, ite_false, Units.val_one]

private theorem tailEntry_ne_zero_of_blockCondition {r : ℕ} (g : G (r + 1))
    (hDiag : (blocks g).toBlocks₁₁ * entryDiagonal r (tailEntry g) = 1) : tailEntry g ≠ 0 := by
  intro h0
  have he := congrFun (congrFun hDiag 0) 0
  simp [entryDiagonal, Matrix.mul_diagonal, h0] at he

private def trailingUnit (h : ℝˣ) : B :=
  ⟨Langlands.GeneralLinear.Iwasawa.diagonalUnits (fun _ : Fin 1 => h), by
    intro i j hij
    exact False.elim ((lt_irrefl i) ((Subsingleton.elim j i) ▸ hij))⟩

private theorem trailingUnit_entry (h : ℝˣ) : (trailingUnit h).val.val 0 0 = h.val := by
  simp [trailingUnit, diagonalUnits_val]

private theorem eq_trailingUnit {h : ℝˣ} {k : B} (hk : k.val.val 0 0 = h.val) :
    trailingUnit h = k := by
  apply Subtype.ext
  apply Units.ext
  ext i j
  obtain rfl : i = 0 := Subsingleton.elim _ _
  obtain rfl : j = 0 := Subsingleton.elim _ _
  rw [trailingUnit_entry, hk]

private theorem mem_rankRaisingSubgroup_iff {r : ℕ} (g : G (r + 1)) :
    g ∈ rankRaisingSubgroup r ↔ (blocks g).toBlocks₁₂ = 0 ∧
      (blocks g).toBlocks₁₁ * entryDiagonal r (tailEntry g) = 1 := by
  constructor
  · rintro ⟨⟨x, h⟩, rfl⟩
    rw [tailEntry, blocks_smoothingMatrix]
    simp only [Matrix.toBlocks_fromBlocks₁₂, Matrix.toBlocks_fromBlocks₁₁,
      Matrix.toBlocks_fromBlocks₂₂, true_and, ← rankRaisingDiagonal_val]
    exact (rankRaisingDiagonal r h).inv_val
  · rintro ⟨hTop, hDiag⟩
    have hne := tailEntry_ne_zero_of_blockCondition g hDiag
    let h := trailingUnit (Units.mk0 (tailEntry g) hne)
    have hh : h.val.val = (blocks g).toBlocks₂₂ := by
      ext i j
      obtain rfl : i = 0 := Subsingleton.elim _ _
      obtain rfl : j = 0 := Subsingleton.elim _ _
      change (trailingUnit (Units.mk0 (tailEntry g) hne)).val.val 0 0 = tailEntry g
      exact trailingUnit_entry _
    refine ⟨((blocks g).toBlocks₂₁, h), blocks_injective ?_⟩
    rw [blocks_smoothingMatrix]
    refine (Matrix.ext_iff_blocks).mpr ⟨?_, by simpa using hTop.symm, by simp, by simpa using hh⟩
    simp only [Matrix.toBlocks_fromBlocks₁₁]
    have hm : (blocks g).toBlocks₁₁ * (rankRaisingDiagonal r h).val = 1 := by
      rw [rankRaisingDiagonal_val, hh]
      exact hDiag
    calc
      _ = ((blocks g).toBlocks₁₁ * (rankRaisingDiagonal r h).val) * (rankRaisingDiagonal r h)⁻¹.val := by
        rw [hm, Matrix.one_mul]
      _ = _ := by
        have hh' : (rankRaisingDiagonal r h).val * (rankRaisingDiagonal r h)⁻¹.val = 1 :=
          (rankRaisingDiagonal r h).val_inv
        rw [Matrix.mul_assoc, hh', Matrix.mul_one]

private theorem continuous_blocks_entry (r : ℕ) (i j : Fin (r + 1) ⊕ Fin 1) :
    Continuous (fun g : G (r + 1) => blocks g i j) := by
  have hv : Continuous (fun g : G (r + 1) => g.val) := Units.continuous_val
  exact (continuous_apply (finSumFinEquiv j)).comp ((continuous_apply (finSumFinEquiv i)).comp hv)

private theorem continuous_entryDiagonal (r : ℕ) : Continuous (entryDiagonal r) := by
  apply Continuous.matrix_diagonal
  apply continuous_pi
  intro i
  by_cases hi : i = 0
  · simp only [hi, ite_true]
    exact continuous_id
  · simp only [hi, ite_false, continuous_const]

/-- The compensating subgroup is closed in the real general linear group. -/
theorem isClosed_rankRaisingSubgroup (r : ℕ) : IsClosed (rankRaisingSubgroup r : Set (G (r + 1))) := by
  let hb := continuous_blocks_entry r
  have hs : Continuous (fun g : G (r + 1) => (blocks g).toBlocks₁₂) :=
    continuous_pi fun i => continuous_pi fun j => hb (.inl i) (.inr j)
  have hl : Continuous (fun g : G (r + 1) => (blocks g).toBlocks₁₁) :=
    continuous_pi fun i => continuous_pi fun j => hb (.inl i) (.inl j)
  have ht : Continuous (fun g : G (r + 1) => entryDiagonal r (tailEntry g)) :=
    (continuous_entryDiagonal r).comp (hb (.inr 0) (.inr 0))
  have he : (rankRaisingSubgroup r : Set (G (r + 1))) =
      {g | (blocks g).toBlocks₁₂ = 0} ∩
      {g | (blocks g).toBlocks₁₁ * entryDiagonal r (tailEntry g) = 1} :=
    Set.ext fun g => mem_rankRaisingSubgroup_iff g
  rw [he]
  exact (isClosed_eq hs continuous_const).inter (isClosed_eq (hl.matrix_mul ht) continuous_const)

private def toRankRaising {r : ℕ} (y : P r) : rankRaisingSubgroup r :=
  ⟨rankRaisingSmoothingMatrix y, ⟨y, rfl⟩⟩

private def fromRankRaising {r : ℕ} (g : rankRaisingSubgroup r) : P r :=
  ((blocks g.val).toBlocks₂₁, trailingUnit (Units.mk0 (tailEntry g.val)
    (tailEntry_ne_zero_of_blockCondition g.val ((mem_rankRaisingSubgroup_iff g.val).mp g.2).2)))

private theorem fromRankRaising_toRankRaising {r : ℕ} (y : P r) :
    fromRankRaising (toRankRaising y) = y := by
  rcases y with ⟨x, h⟩
  apply Prod.ext
  · change (blocks (rankRaisingSmoothingMatrix (x, h))).toBlocks₂₁ = x
    rw [blocks_smoothingMatrix, Matrix.toBlocks_fromBlocks₂₁]
  · apply eq_trailingUnit
    change h.val.val 0 0 = tailEntry (rankRaisingSmoothingMatrix (x, h))
    rw [tailEntry, blocks_smoothingMatrix]
    rfl

/-- The compensating subgroup parametrized by its bottom row and invertible last entry. -/
def rankRaisingHomeomorph (r : ℕ) : P r ≃ₜ rankRaisingSubgroup r where
  toFun := toRankRaising
  invFun := fromRankRaising
  left_inv := fromRankRaising_toRankRaising
  right_inv := by
    intro g
    obtain ⟨p, hp⟩ := g.property
    have hg : toRankRaising p = g := Subtype.ext hp
    rw [← hg, fromRankRaising_toRankRaising]
  continuous_toFun := by
    unfold toRankRaising
    apply Continuous.subtype_mk
    have hTail : Continuous (fun h : B => h.val.val 0 0) := by
      have hv : Continuous (fun h : B => h.val.val) := Units.continuous_val.comp continuous_subtype_val
      exact (continuous_apply 0).comp ((continuous_apply 0).comp hv)
    have hd : Continuous (rankRaisingDiagonal r : B → G r) := by
      apply Units.isOpenEmbedding_val.isInducing.continuous_iff.mpr
      change Continuous (fun h : B => (rankRaisingDiagonal r h).val)
      simp_rw [rankRaisingDiagonal_val]
      exact (continuous_entryDiagonal r).comp hTail
    exact continuous_lowerBlockPair.comp (((hd.comp continuous_snd).inv).prodMk continuous_id)
  continuous_invFun := by
    unfold fromRankRaising
    apply Continuous.prodMk
    · exact continuous_pi fun i => continuous_pi fun j =>
        (continuous_blocks_entry r (.inr i) (.inl j)).comp continuous_subtype_val
    · unfold trailingUnit
      apply Continuous.subtype_mk
      apply Units.isOpenEmbedding_val.isInducing.continuous_iff.mpr
      change Continuous (fun g : rankRaisingSubgroup r =>
        Matrix.diagonal (fun _ : Fin 1 => tailEntry g.val))
      exact Continuous.matrix_diagonal <| continuous_pi fun _ =>
        (continuous_blocks_entry r (.inr 0) (.inr 0)).comp continuous_subtype_val

@[simp]
theorem rankRaisingHomeomorph_apply_val (r : ℕ) (p : P r) :
    (rankRaisingHomeomorph r p).val = rankRaisingSmoothingMatrix p := rfl

/-- The real rank-raising subgroup is closed, has an exponential Lie algebra and is
homeomorphic to its row and invertible trailing coordinates. -/
def RealRankRaisingSubgroupStatement : Prop :=
  ∀ r : ℕ, (∃ (h : IsClosed (rankRaisingSubgroup r : Set (G (r + 1)))),
    IsExpLieAlgebra (rankRaisingSubgroup r) (lieSubmodule _ h)) ∧
    ∃ T : P r ≃ₜ rankRaisingSubgroup r, ∀ p : P r, (T p).val = rankRaisingSmoothingMatrix p

theorem realRankRaisingSubgroup : RealRankRaisingSubgroupStatement := by
  intro r
  exact ⟨⟨isClosed_rankRaisingSubgroup r, isExpLieAlgebra_of_isClosed _ (isClosed_rankRaisingSubgroup r)⟩,
    rankRaisingHomeomorph r, rankRaisingHomeomorph_apply_val r⟩

end Langlands.Global.RankinSelbergGlobal.RealRankRaisingIntegral
