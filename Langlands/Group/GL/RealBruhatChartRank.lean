import Langlands.Group.GL.RealBruhatProductChart
import Langlands.Group.GL.UpperBruhatFiltrationGeometryProof
import Langlands.Group.GL.UpperBruhatRankOrderProof

/-! # The real Bruhat product chart lies in the cell and the higher layers -/

noncomputable section

open Set Langlands.GeneralLinear
open scoped Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.GeneralLinear.RealBruhatChartRank

open RealBruhatProductChart RealBruhatTrailingChart UpperBruhatRank

variable {n : ℕ}
local notation "M" => Matrix (Fin n) (Fin n) ℝ
local notation "G" => Langlands.GeneralLinear n ℝ

private theorem count_le_rank_corner_mul_permutation (w : Equiv.Perm (Fin n))
    (l : G) (h₁ : ∀ i j : Fin n, i < j → l.val i j = 0)
    (h₂ : ∀ i : Fin n, l.val i i = 1) (i j : Fin (n + 1)) :
    count w i j.val ≤ (corner i j (l * permutation n ℝ w).val).rank := by
  let C := {c : Fin n // c.val < j.val ∧ i.val ≤ (w c).val}
  let R := {d : Fin n // i.val ≤ d.val ∧ (w⁻¹ d).val < j.val}
  let e : C ≃ R :=
    { toFun := fun c => ⟨w c, c.property.2, by simpa using c.property.1⟩
      invFun := fun d => ⟨w⁻¹ d, d.property.2, by simpa using d.property.1⟩
      left_inv := fun c => Subtype.ext (by simp)
      right_inv := fun d => Subtype.ext (by simp) }
  let Y := corner i j (l * permutation n ℝ w).val
  let A : Matrix R R ℝ := l.val.submatrix Subtype.val Subtype.val
  have hA : Y.submatrix (Subtype.val : R → Fin n) (fun d => w⁻¹ d.val) = A := by
    ext d d'
    change (if i.val ≤ d.val.val ∧ (w⁻¹ d'.val).val < j.val then
      (l * permutation n ℝ w).val d.val (w⁻¹ d'.val) else 0) = l.val d.val d'.val
    rw [ite_eq_left ⟨d.property.1, d'.property.2⟩, mul_permutation_entry]
    simp
  have hAtri : A.transpose.IsUpperTriangular := fun d d' h => h₁ _ _ h
  have hdet : A.det = 1 := by
    rw [← Matrix.det_transpose, Matrix.det_of_isUpperTriangular hAtri]
    simp [A, h₂]
  have hcount : count w i j.val = Fintype.card R := by
    have hc : count w i j.val = Fintype.card C := by
      rw [Fintype.card_subtype]
      rfl
    exact hc.trans (Fintype.card_congr e)
  rw [hcount, ← Matrix.rank_of_det_ne_zero (hdet.trans_ne one_ne_zero), ← hA]
  exact Matrix.rank_submatrix_le _ _ _

/-- Any invertible matrix in the real product chart of `w` is either in
the cell of `w` or in a cell with strictly more inversions. -/
theorem mem_cellNeighborhood_of_mem_productChart_target (w : Equiv.Perm (Fin n)) (g : G)
    (hg : g.val ∈ (productChart w).target) : g ∈ upperBruhatCellNeighborhood n ℝ w := by
  let e := productChart w
  let z := e.symm g.val
  let Y := combine w z
  let B : M := upperProjection n Y
  let L : M := lowerFactorOfCoordinates Y
  have hz : z ∈ e.source := e.map_target hg
  have hb : B.IsUpperTriangular := by
    intro i j hij
    simp [B, show j < i from hij]
  have hbU : IsUnit B := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_of_isUpperTriangular hb, isUnit_iff_ne_zero]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => by simpa [B, Y] using hz.1 i
  have hl₁ (i j : Fin n) (hij : i < j) : L i j = 0 := by
    simp [L, lowerFactorOfCoordinates, Matrix.one_apply_ne hij.ne, not_lt_of_ge hij.le]
  have hl₂ (i : Fin n) : L i i = 1 := by
    simp [L, lowerFactorOfCoordinates]
  have hlU : IsUnit L := by
    have ht : L.transpose.IsUpperTriangular := fun i j hij => hl₁ j i hij
    rw [Matrix.isUnit_iff_isUnit_det, ← Matrix.det_transpose, Matrix.det_of_isUpperTriangular ht]
    simp [hl₂]
  let b : G := hbU.unit
  let l : G := hlU.unit
  have hbv : b.val = B := IsUnit.unit_spec _
  have hlv : l.val = L := IsUnit.unit_spec _
  have hb' : b ∈ upperTriangularSubgroup n ℝ := by
    change b.val.IsUpperTriangular
    rwa [hbv]
  have he : g.val = b.val * (l * permutation n ℝ w).val := by
    rw [Units.val_mul, hbv, hlv, ← Matrix.mul_assoc]
    exact (e.right_inv hg).symm
  obtain ⟨v, hv⟩ := exists_mem_upperBruhatCell g
  by_cases hvw : v = w
  · exact Or.inl (hvw ▸ hv)
  · refine Or.inr ⟨v, upperBruhatRankOrderInversion n w v (Ne.symm hvw) ?_, hv⟩
    intro i j
    have hr : (corner i j g.val).rank = count v i j.val := by
      rw [← rank_corner_permutation (K := ℝ)]
      exact ((upperBruhatRankCharacterization ℝ n v g).mp hv i j)
    rw [← hr, he, rank_corner_triangular_mul i j hb']
    exact count_le_rank_corner_mul_permutation w l
      (fun i j hij => hlv.symm ▸ hl₁ i j hij) (fun i => hlv.symm ▸ hl₂ i) i j

/-- The entire chart for a real Bruhat cell is contained in its open
neighborhood formed with the strictly higher inversion layers. -/
def RealBruhatChartRankStatement : Prop :=
  ∀ (n : ℕ) (w : Equiv.Perm (Fin n)) (g : Langlands.GeneralLinear n ℝ),
    g.val ∈ (productChart w).target → g ∈ upperBruhatCellNeighborhood n ℝ w

theorem realBruhatChartRank : RealBruhatChartRankStatement :=
  fun _ => mem_cellNeighborhood_of_mem_productChart_target

end Langlands.GeneralLinear.RealBruhatChartRank
