import Langlands.GroupScheme.SpecialLinear
import Langlands.GroupScheme.AutomorphicAction.LocallyInner
import Langlands.GroupScheme.Reductive.UnitPowerFppfCover
import Langlands.GroupScheme.MatrixRepresentation.SchemeAction

/-! # Invertible matrix conjugation is fppf-locally special-linear conjugation -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.SpecialLinear

open Matrix.GeneralLinearGroup (scalar scalar_commute det det_scalar val_det_apply map_det map_scalar)

variable {k : Type u} [Field k] {I : Type} [Fintype I] [DecidableEq I]

local notation "R" => CommRingCat.of k
local notation "SL" => groupScheme I R

/-- A single base-field matrix implements the automorphism on every scheme test. -/
def HasUniformMatrixConjugation (F : SL ≅ SL) (C : GL I k) : Prop :=
  ∀ (T : Over (Spec R)) (x : T ⟶ (SL).X),
    let C_T := Matrix.GeneralLinearGroup.map (scalarMap T) C
    C_T * Matrix.SpecialLinearGroup.toGL (pointsEquiv I R T x) =
      Matrix.SpecialLinearGroup.toGL (pointsEquiv I R T (x ≫ F.hom.hom.hom)) * C_T

/-- On the fppf cover adjoining a determinant-normalizing root, the same
conjugation is given by an actual point of the special-linear group. -/
theorem isFppfLocallyInner_of_uniformMatrixConjugation [Nonempty I]
    {F : SL ≅ SL} {C : GL I k} (hC : HasUniformMatrixConjugation F C) :
    IsFppfLocallyInner F := by
  let Z : Over (Spec R) := Over.mk (𝟙 (Spec R))
  let : IsAffine Z.left := inferInstanceAs (IsAffine (Spec R))
  let Cmap (T : Over (Spec R)) := Matrix.GeneralLinearGroup.map (scalarMap T) C
  have hmap {T W : Over (Spec R)} (t : W ⟶ T) :
      Matrix.GeneralLinearGroup.map t.left.appTop.hom (Cmap T) = Cmap W := by
    apply Units.ext
    ext i j
    exact scalarMap_naturality t _
  obtain ⟨U, j, _, hf, hs, hp, r, hr⟩ := UnitPowerExtension.exists_roots_test Z
    (Fintype.card I) Fintype.card_ne_zero (fun _ : Fin 1 => (det (Cmap Z))⁻¹)
  have hnorm : r 0 ^ Fintype.card I = (det (Cmap U))⁻¹ := by
    rw [hr 0, map_inv]
    exact congrArg Inv.inv ((map_det j.left.appTop.hom (Cmap Z)).symm.trans
      (congrArg det (hmap j)))
  let B := scalar I (r 0) * Cmap U
  have hdet : det B = 1 := by
    change det (scalar I (r 0) * Cmap U) = 1
    rw [map_mul, det_scalar, hnorm, inv_mul_cancel]
  let y := (pointsEquiv I R U).symm ⟨B.val, by rw [← val_det_apply, hdet]; rfl⟩
  have hy : Matrix.SpecialLinearGroup.toGL (pointsEquiv I R U y) = B := by
    rw [show pointsEquiv I R U y = ⟨B.val, by rw [← val_det_apply, hdet]; rfl⟩ from
      (pointsEquiv I R U).apply_symm_apply _]
    exact Units.ext rfl
  have hstruct : U.hom = j.left := by
    have h : j.left ≫ 𝟙 (Spec R) = U.hom := Over.w j
    exact h.symm.trans (Category.comp_id (j.left : U.left ⟶ Spec R))
  refine ⟨U, hstruct ▸ hf, hstruct ▸ hs, hstruct ▸ hp, y, ?_⟩
  intro W t x
  simp only [AutomorphicAction.conjugation_act, Grp.id_hom_hom, Category.comp_id]
  apply (pointsEquiv I R W).injective
  apply Matrix.SpecialLinearGroup.toGL_injective
  have hty : Matrix.SpecialLinearGroup.toGL (pointsEquiv I R W (t ≫ y)) =
      scalar I (Units.map t.left.appTop.hom.toMonoidHom (r 0)) * Cmap W := by
    rw [pointsEquiv_naturality]
    have htoGL (g : Matrix.SpecialLinearGroup I Γ(U.left, ⊤)) :
        Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map t.left.appTop.hom g) =
          Matrix.GeneralLinearGroup.map t.left.appTop.hom (Matrix.SpecialLinearGroup.toGL g) :=
      Units.ext rfl
    rw [htoGL, hy]
    simp only [B, map_mul, map_scalar, hmap t]
    rfl
  let D := scalar I (Units.map t.left.appTop.hom.toMonoidHom (r 0))
  let X := Matrix.SpecialLinearGroup.toGL (pointsEquiv I R W x)
  let Y := Matrix.SpecialLinearGroup.toGL (pointsEquiv I R W (x ≫ F.hom.hom.hom))
  have hXY : Cmap W * X = Y * Cmap W := hC W x
  simp only [map_mul, map_inv, hty]
  change D * Cmap W * X * (D * Cmap W)⁻¹ = Y
  rw [mul_assoc D, hXY, ← mul_assoc D Y, scalar_commute _ Y, mul_assoc Y,
    mul_inv_cancel_right]

end Langlands.GroupScheme.SpecialLinear
