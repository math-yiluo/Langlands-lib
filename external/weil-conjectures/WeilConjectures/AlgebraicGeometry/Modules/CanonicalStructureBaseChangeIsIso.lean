/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
import WeilConjectures.AlgebraicGeometry.AffinePushforwardBaseChangeIsIso
import WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

/-! # Invertibility of the canonical structure-sheaf base-change comparison

## References

* Stacks Project, Tag 02KG, and Tags 0096 and 01CA for the structure-sheaf pullback
-/

@[expose] public section

noncomputable section
universe u
set_option autoImplicit false
open CategoryTheory SheafOfModules
namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The adjoint of restriction along a cartesian square with affine vertical map is invertible.
-/
theorem canonical_structure_baseChange_isIso {X Y X' Y' : Scheme.{u}}
    (p : X ⟶ Y) (q : X' ⟶ Y') (g : Y' ⟶ Y) (k : X' ⟶ X)
    (sq : IsPullback k q p g) [IsAffineHom p] :
    IsIso (((pullbackPushforwardAdjunction g).homEquiv _ _).symm
      ((pushforward p).map (SheafOfModules.unitToPushforwardObjUnit k.toRingCatSheafHom) ≫
        (pushforwardComp k p).hom.app (unit X') ≫
        (pushforwardCongr sq.w).hom.app (unit X') ≫
        (pushforwardComp q g).inv.app (unit X'))) := by
  let adj := Classical.choose (exists_tensorPullbackAdjunction g)
  let E := (pushforward p).obj (unit X)
  let β := moduleBaseChangeMap p q g k sq.w (unit X)
  let ε := tensorPullbackObjUnitToUnit k
  have := SheafOfModules.isQuasicoherent_unit (R := X.ringCatSheaf)
  have : IsIso β := affinePushforward_baseChange_isIso p q g k sq (unit X)
  have : IsIso ε := (tensorPullbackObjUnitToUnit_isIso k).1
  let b := ((pullbackPushforwardAdjunction g).homEquiv _ _).symm
    ((pushforward p).map (SheafOfModules.unitToPushforwardObjUnit k.toRingCatSheafHom) ≫
      (pushforwardComp k p).hom.app (unit X') ≫
      (pushforwardCongr sq.w).hom.app (unit X') ≫
      (pushforwardComp q g).inv.app (unit X'))
  have hb : b = (Adjunction.leftAdjointUniq (pullbackPushforwardAdjunction g) adj).hom.app E ≫
      β ≫ (pushforward q).map ε := by
    apply ((pullbackPushforwardAdjunction g).homEquiv _ _).injective
    dsimp only [b]
    rw [Equiv.apply_symm_apply, Adjunction.homEquiv_naturality_right,
      Adjunction.homEquiv_leftAdjointUniq_hom_app]
    rw [← adj.homEquiv_unit]
    dsimp only [β, moduleBaseChangeMap]
    rw [Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply]
    simp only [Category.assoc]
    rw [← Functor.comp_map]
    rw [← (pushforwardComp q g).inv.naturality ε]
    rw [← (pushforwardCongr sq.w).hom.naturality_assoc ε]
    rw [← (pushforwardComp k p).hom.naturality_assoc ε]
    simp only [Functor.comp_map]
    rw [← Functor.map_comp_assoc, (tensorPullbackObjUnitToUnit_isIso k).2]
  change IsIso b
  rw [hb]
  infer_instance

end AlgebraicGeometry.Scheme.Modules
