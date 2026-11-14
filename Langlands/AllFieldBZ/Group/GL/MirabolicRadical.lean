import Langlands.AllFieldBZ.Group.GL.RankMaps
import Langlands.Group.GL.MirabolicRadical

/-!
# All-field port of `Langlands.Group.GL.MirabolicRadical`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Group.GL.MirabolicRadical` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
namespace Langlands.AllFieldBZ.GeneralLinear.Mirabolic
open Langlands.GeneralLinear.Mirabolic
universe u

variable {F : Type u} [CommRing F] {n : ℕ}

private theorem _root_.Langlands.GeneralLinear.Mirabolic.fixedColumn_mul (g h : Langlands.GeneralLinear (n + 1) F)
    (hh : ∀ i (j : Fin n), h.val i j.castSucc = if i = j.castSucc then 1 else 0)
    (i : Fin (n + 1)) (j : Fin n) :
    (g * h).val i j.castSucc = g.val i j.castSucc := by
  change (g.val * h.val) i j.castSucc = _
  simp [Matrix.mul_apply, hh]

private def _root_.Langlands.GeneralLinear.Mirabolic.columnUnit (v : Fin n → F) :
    Matrix.GeneralLinearGroup (Fin n ⊕ Fin 1) F where
  val := Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) F) (Matrix.of fun i (_ : Fin 1) => v i) 0 (1 : Matrix (Fin 1) (Fin 1) F)
  inv := Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) F) (Matrix.of fun i (_ : Fin 1) => -v i) 0 (1 : Matrix (Fin 1) (Fin 1) F)
  val_inv := by
    simp [Matrix.fromBlocks_multiply, Pi.add_def]
    exact Matrix.fromBlocks_one
  inv_val := by
    simp [Matrix.fromBlocks_multiply, Pi.add_def]
    exact Matrix.fromBlocks_one

private def _root_.Langlands.GeneralLinear.Mirabolic.columnGL (v : Fin n → F) : Langlands.GeneralLinear (n + 1) F :=
  Langlands.GeneralLinear.reindex finSumFinEquiv (columnUnit v)

private theorem _root_.Langlands.GeneralLinear.Mirabolic.columnGL_first (v : Fin n → F) (i : Fin (n + 1)) (j : Fin n) :
    (columnGL v).val i j.castSucc = if i = j.castSucc then 1 else 0 := by
  refine Fin.lastCases ?_ (fun i => ?_) i
  · change Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) F) (Matrix.of fun i (_ : Fin 1) => v i) 0 (1 : Matrix (Fin 1) (Fin 1) F)
      (finSumFinEquiv.symm (Fin.natAdd n (0 : Fin 1)))
      (finSumFinEquiv.symm (j.castAdd 1)) = _
    simp [(Fin.castSucc_ne_last _).symm]
  · change Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) F) (Matrix.of fun i (_ : Fin 1) => v i) 0 (1 : Matrix (Fin 1) (Fin 1) F)
      (finSumFinEquiv.symm (i.castAdd 1)) (finSumFinEquiv.symm (j.castAdd 1)) = _
    simp [Matrix.one_apply]

private theorem _root_.Langlands.GeneralLinear.Mirabolic.columnGL_last (v : Fin n → F) (i : Fin n) :
    (columnGL v).val i.castSucc (Fin.last n) = v i := by
  change Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) F) (Matrix.of fun i (_ : Fin 1) => v i) 0 (1 : Matrix (Fin 1) (Fin 1) F)
    (finSumFinEquiv.symm (i.castAdd 1))
    (finSumFinEquiv.symm (Fin.natAdd n (0 : Fin 1))) = _
  simp

private theorem _root_.Langlands.GeneralLinear.Mirabolic.columnGL_bottom (v : Fin n → F) (j : Fin (n + 1)) :
    (columnGL v).val (Fin.last n) j = if j = Fin.last n then 1 else 0 := by
  refine Fin.lastCases ?_ (fun j => ?_) j
  · change Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) F) (Matrix.of fun i (_ : Fin 1) => v i) 0 (1 : Matrix (Fin 1) (Fin 1) F)
      (finSumFinEquiv.symm (Fin.natAdd n (0 : Fin 1)))
      (finSumFinEquiv.symm (Fin.natAdd n (0 : Fin 1))) = _
    simp
  · rw [columnGL_first]
    simp [(Fin.castSucc_ne_last _).symm]

private theorem _root_.Langlands.GeneralLinear.Mirabolic.levi_conjugate_mem (g : Langlands.GeneralLinear n F)
    (u : Langlands.GeneralLinear.mirabolic n F) (hu : u ∈ radical n F) :
    levi g * u * (levi g)⁻¹ ∈ radical n F := by
  let v := radicalCoordinates (⟨u, hu⟩ : radical n F)
  have he : (radicalElement v).val = u := congrArg Subtype.val
    (radicalElement_coordinates (⟨u, hu⟩ : radical n F))
  rw [← he, levi_conjugate_radicalElement]
  exact (radicalElement _).property

section Topology
variable [TopologicalSpace F]

private theorem _root_.Langlands.GeneralLinear.Mirabolic.continuous_leviEquiv_symm :
    Continuous ((leviEquiv (n := n) (F := F)).symm) := by
  apply Units.continuous_iff.mpr
  constructor
  · apply continuous_matrix
    intro i j
    change Continuous (fun g : leviSubgroup n F => (leviEquiv.symm g).val i j)
    simp_rw [leviEquiv_symm_entry]
    exact (entry (F := F) i.castSucc j.castSucc).continuous.comp continuous_subtype_val
  · apply continuous_matrix
    intro i j
    have hc : Continuous (fun g : leviSubgroup n F =>
        (g.val.val⁻¹).val i.castSucc j.castSucc) :=
      ((continuous_apply j.castSucc).comp ((continuous_apply i.castSucc).comp
        (show Continuous (fun g : Langlands.GeneralLinear (n + 1) F => (g⁻¹).val) from
          Units.continuous_coe_inv))).comp
            (continuous_subtype_val.comp continuous_subtype_val)
    convert hc using 1
    funext g
    rw [← map_inv, leviEquiv_symm_entry]
    rfl

private theorem _root_.Langlands.GeneralLinear.Mirabolic.continuous_successorEquiv_symm :
    Continuous ((successorEquiv (n := n) (F := F)).symm) := by
  apply Continuous.subtype_mk
  apply Units.continuous_iff.mpr
  constructor
  · apply continuous_matrix
    intro i j
    change Continuous (fun g : successorSubgroup n F => (successorEquiv.symm g).val.val i j)
    simp_rw [successorEquiv_symm_entry]
    exact (entry (F := F) i.castSucc j.castSucc).continuous.comp continuous_subtype_val
  · apply continuous_matrix
    intro i j
    have hc : Continuous (fun g : successorSubgroup n F =>
        (g.val.val⁻¹).val i.castSucc j.castSucc) :=
      ((continuous_apply j.castSucc).comp ((continuous_apply i.castSucc).comp
        (show Continuous (fun g : Langlands.GeneralLinear (n + 1 + 1) F => (g⁻¹).val) from
          Units.continuous_coe_inv))).comp
            (continuous_subtype_val.comp continuous_subtype_val)
    convert hc using 1
    funext g
    change ((successorEquiv.symm g)⁻¹).val.val i j = _
    rw [← map_inv, successorEquiv_symm_entry]
    rfl

variable [IsTopologicalRing F]

private theorem _root_.Langlands.GeneralLinear.Mirabolic.continuous_columnUnit :
    Continuous (columnUnit (n := n) (F := F)) := by
  apply Units.continuous_iff.mpr
  constructor
  · apply continuous_matrix
    rintro (i | i) (j | j)
    · exact continuous_const
    · exact continuous_apply i
    · exact continuous_const
    · exact continuous_const
  · apply continuous_matrix
    rintro (i | i) (j | j)
    · exact continuous_const
    · exact (continuous_apply i).neg
    · exact continuous_const
    · exact continuous_const

end Topology
end Langlands.AllFieldBZ.GeneralLinear.Mirabolic
