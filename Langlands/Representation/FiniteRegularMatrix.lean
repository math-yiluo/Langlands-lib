import Langlands.Representation.FiniteRegularSemisimplicity
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-! # Finite-coordinate matrices for a finite regular representation -/

noncomputable section

universe u

namespace Langlands.FiniteQuotientAveraging

open Representation
open scoped Matrix

variable (k Q : Type u) [Field k] [Group Q] [Fintype Q]

/-- Enumerating a finite group gives finite coordinates on its function space. -/
def regularCoordinateEquiv : (Q → k) ≃ₗ[k] (Fin (Fintype.card Q) → k) :=
  LinearEquiv.piCongrLeft' k (fun _ : Q => k) (Fintype.equivFin Q)

/-- The function regular representation transported to finite coordinates. -/
def coordinateRegular : Representation k Q (Fin (Fintype.card Q) → k) :=
  (regularCoordinateEquiv k Q).conjRingEquiv.toMonoidHom.comp
    (TannakaDuality.FiniteGroup.leftRegular (k := k) (G := Q))

theorem coordinateRegular_apply (g : Q) (v : Fin (Fintype.card Q) → k) :
    coordinateRegular k Q g v =
      regularCoordinateEquiv k Q
        (TannakaDuality.FiniteGroup.leftRegular g
          ((regularCoordinateEquiv k Q).symm v)) := rfl

/-- The actual invertible matrices for the finite-coordinate regular action. -/
def regularMatrixHom : Q →* GL (Fin (Fintype.card Q)) k :=
  MonoidHom.toHomUnits
    (((Matrix.toLinAlgEquiv' :
      Matrix (Fin (Fintype.card Q)) (Fin (Fintype.card Q)) k ≃ₐ[k]
        Module.End k (Fin (Fintype.card Q) → k)).symm.toMonoidHom).comp
          (coordinateRegular k Q))

/-- Matrix multiplication is the transported function regular action. -/
theorem regularMatrixHom_mulVec (g : Q) (v : Fin (Fintype.card Q) → k) :
    (regularMatrixHom k Q g : Matrix (Fin (Fintype.card Q)) (Fin (Fintype.card Q)) k)
        *ᵥ v = coordinateRegular k Q g v := by
  change Matrix.toLinAlgEquiv'
    (Matrix.toLinAlgEquiv'.symm (coordinateRegular k Q g)) v = _
  rw [AlgEquiv.apply_symm_apply]

/-- Reindexing the regular action preserves its complete subrepresentation lattice. -/
def regularSubrepresentationOrderIso :
    Subrepresentation (coordinateRegular k Q) ≃o
      Subrepresentation (TannakaDuality.FiniteGroup.leftRegular (k := k) (G := Q)) where
  toFun W :=
    { toSubmodule := W.toSubmodule.comap (regularCoordinateEquiv k Q).toLinearMap
      apply_mem_toSubmodule g v hv := by
        change (regularCoordinateEquiv k Q)
          (TannakaDuality.FiniteGroup.leftRegular g v) ∈ W.toSubmodule
        have h := W.apply_mem_toSubmodule g hv
        change coordinateRegular k Q g ((regularCoordinateEquiv k Q) v) ∈ W.toSubmodule at h
        rwa [coordinateRegular_apply, LinearEquiv.symm_apply_apply] at h }
  invFun W :=
    { toSubmodule := W.toSubmodule.comap (regularCoordinateEquiv k Q).symm.toLinearMap
      apply_mem_toSubmodule g v hv := by
        change (regularCoordinateEquiv k Q).symm (coordinateRegular k Q g v) ∈ W.toSubmodule
        rw [coordinateRegular_apply, LinearEquiv.symm_apply_apply]
        have h := W.apply_mem_toSubmodule g hv
        exact h }
  left_inv W := by
    apply Subrepresentation.toSubmodule_injective
    ext v
    simp only [Submodule.mem_comap, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply]
  right_inv W := by
    apply Subrepresentation.toSubmodule_injective
    ext v
    simp only [Submodule.mem_comap, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply]
  map_rel_iff' {W U} := by
    constructor
    · intro h v hv
      change v ∈ U.toSubmodule
      have hv' : (regularCoordinateEquiv k Q).symm v ∈
          W.toSubmodule.comap (regularCoordinateEquiv k Q).toLinearMap := by
        change (regularCoordinateEquiv k Q) ((regularCoordinateEquiv k Q).symm v) ∈ W.toSubmodule
        rw [LinearEquiv.apply_symm_apply]
        exact hv
      have h' := h hv'
      change (regularCoordinateEquiv k Q) ((regularCoordinateEquiv k Q).symm v) ∈ U.toSubmodule at h'
      rwa [LinearEquiv.apply_symm_apply] at h'
    · intro h v hv
      exact h hv

/-- The finite-coordinate regular representation has the same order obstruction. -/
theorem coordinateRegular_isSemisimple_iff_card_ne_zero :
    IsSemisimpleRepresentation (coordinateRegular k Q) ↔ (Nat.card Q : k) ≠ 0 :=
  (regularSubrepresentationOrderIso k Q).complementedLattice_iff.trans
    (regular_isSemisimple_iff_card_ne_zero k Q)

/-- In characteristic `p`, the finite-coordinate regular representation is
semisimple exactly when `p` does not divide the group order. -/
theorem coordinateRegular_isSemisimple_iff_not_dvd (p : ℕ) [CharP k p] :
    IsSemisimpleRepresentation (coordinateRegular k Q) ↔ ¬ p ∣ Nat.card Q :=
  (coordinateRegular_isSemisimple_iff_card_ne_zero k Q).trans
    (CharP.cast_eq_zero_iff k p (Nat.card Q)).not

end Langlands.FiniteQuotientAveraging
