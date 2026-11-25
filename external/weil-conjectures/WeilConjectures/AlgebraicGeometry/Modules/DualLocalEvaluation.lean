/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Modules.Dual
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.Bidual

/-! # Evaluation of the internal dual on a finite-free open

3.

## References

* Stacks Project, Tag 0BRT
-/

@[expose] public section

universe u

open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
private theorem evaluation_bijective_of_generators (X : Scheme.{u}) (M : X.Modules)
    (V : X.Opens) (I : Type u) [Fintype I]
    (s : I → ((PresheafOfModules.restrictOver X.sheaf.obj V).obj
      (PresheafOfModules.unit _) ⟶ (PresheafOfModules.restrictOver X.sheaf.obj V).obj M.val))
    (t : I → ((PresheafOfModules.restrictOver X.sheaf.obj V).obj M.val ⟶
      (PresheafOfModules.restrictOver X.sheaf.obj V).obj (PresheafOfModules.unit _)))
    (htot : ∑ i, t i ≫ s i = 𝟙 _) :
    Function.Bijective (PresheafOfModules.homObjEvalId M.val
      (PresheafOfModules.unit _) V) := by
  classical
  let T : (Over V)ᵒᵖ := op (Over.mk (𝟙 V))
  let m : I → M.val.obj (op V) := fun i ↦ (s i).app T (1 : X.sheaf.obj.obj (op V))
  have hspan (W : (Over V)ᵒᵖ) (x : M.val.obj (op W.unop.left)) :
      x = ∑ i, (show X.sheaf.obj.obj (op W.unop.left) from (t i).app W x) •
        (show M.val.obj (op W.unop.left) from M.val.map W.unop.hom.op (m i)) := by
    have h : ∑ i, (t i ≫ s i).app W x = x :=
      (PresheafOfModules.sum_app_apply Finset.univ (fun i ↦ t i ≫ s i) W x).symm.trans
        (congrArg (fun f ↦ f.app W x) htot)
    exact h.symm.trans (Finset.sum_congr rfl fun i _ ↦
      PresheafOfModules.app_unit_eq_smul (s i) W _)
  constructor
  · rw [injective_iff_map_eq_zero]
    intro φ hφ
    refine PresheafOfModules.hom_ext fun W ↦ ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
    have hm (i : I) : φ.app W (M.val.map W.unop.hom.op (m i)) = 0 := by
      have hz : φ.app T (m i) = 0 := congrArg (fun f ↦ f (m i)) hφ
      exact (PresheafOfModules.naturality_apply φ
        (Over.homMk W.unop.hom (Category.comp_id _) : W.unop ⟶ Over.mk (𝟙 V)).op
        (m i)).trans ((congrArg _ hz).trans (map_zero _))
    change φ.app W x = 0
    rw [hspan W x, map_sum]
    exact Finset.sum_eq_zero fun i _ ↦ by rw [(φ.app W).hom.map_smul, hm, smul_zero]
  · intro l
    change Module.Dual (X.sheaf.obj.obj (op V)) (M.val.obj (op V)) at l
    refine ⟨∑ i, (show X.sheaf.obj.obj (op V) from l (m i)) • t i, ?_⟩
    apply LinearMap.ext
    intro x
    change (∑ i, (show X.sheaf.obj.obj (op V) from l (m i)) • t i).app T x = l x
    rw [PresheafOfModules.sum_app_apply]
    have hx : x = ∑ i, (show X.sheaf.obj.obj (op V) from (t i).app T x) • m i := by
      have h := hspan T x
      change x = ∑ i, (show X.sheaf.obj.obj (op V) from (t i).app T x) •
        (show M.val.obj (op V) from M.val.map (𝟙 (op V)) (m i)) at h
      have hid (z : M.val.obj (op V)) :
          (show M.val.obj (op V) from M.val.map (𝟙 (op V)) z) = z := by
        rw [M.val.map_id]
        rfl
      simpa only [hid] using h
    calc
      _ = ∑ i, l (m i) * (show X.sheaf.obj.obj (op V) from (t i).app T x) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [PresheafOfModules.restrictOver_smul_app_apply]
        change X.sheaf.obj.map (𝟙 (op V)) (l (m i)) * _ = _
        rw [X.sheaf.obj.map_id]
        rfl
      _ = ∑ i, (show X.sheaf.obj.obj (op V) from (t i).app T x) • l (m i) := by
        apply Finset.sum_congr rfl
        intro i _
        exact mul_comm _ _
      _ = l (∑ i, (show X.sheaf.obj.obj (op V) from (t i).app T x) • m i) := by
        rw [map_sum]
        exact Finset.sum_congr rfl fun i _ ↦ (l.map_smul _ _).symm
      _ = l x := congrArg l hx.symm

set_option backward.isDefEq.respectTransparency false in
/-- Evaluation identifies the internal dual with the dual of sections on a finite-free open. -/
theorem dual_local_evaluation_equiv (X : Scheme.{u}) (M : X.Modules)
    (U : X.Opens) (I : Type u) [Finite I]
    (e : M.over U ≅ SheafOfModules.free I) (V : X.Opens) (g : V ⟶ U) :
    ∃ c : (dual M).val.obj (op V) ≃ₗ[X.presheaf.obj (op V)]
        Module.Dual (X.presheaf.obj (op V)) (M.val.obj (op V)),
      ∀ (ψ : (dual M).val.obj (op V)) (x : M.val.obj (op V)),
        c ψ x = ψ.app (op (Over.mk (𝟙 V))) x := by
  classical
  let := Fintype.ofFinite I
  let S (i : I) : (SheafOfModules.unit X.ringCatSheaf).over U ⟶ M.over U :=
    SheafOfModules.ιFree i ≫ e.inv
  let C (i : I) : M.over U ⟶ (SheafOfModules.unit X.ringCatSheaf).over U :=
    e.hom ≫ SheafOfModules.freeπ i
  have htot : ∑ i, C i ≫ S i = 𝟙 _ := by
    calc
      _ = e.hom ≫ (∑ i : I, SheafOfModules.freeπ i ≫ SheafOfModules.ιFree i) ≫ e.inv := by
        simp only [C, S, Category.assoc, Preadditive.comp_sum, Preadditive.sum_comp]
      _ = 𝟙 _ := by rw [SheafOfModules.sum_freeπ_ιFree, Category.id_comp, Iso.hom_inv_id]
  let s := fun i ↦ PresheafOfModules.restrictOverMap g
    (SheafOfModules.toRestrictOverHom.{u} (R := X.sheaf) (S i))
  let t := fun i ↦ PresheafOfModules.restrictOverMap g
    (SheafOfModules.toRestrictOverHom.{u} (R := X.sheaf) (C i))
  have htotal : ∑ i, t i ≫ s i = 𝟙 _ := by
    change ∑ i, PresheafOfModules.restrictOverMap g
      (SheafOfModules.toRestrictOverHom.{u} (R := X.sheaf) (C i ≫ S i)) = 𝟙 _
    have hU : ∑ i, SheafOfModules.toRestrictOverHom.{u} (R := X.sheaf) (C i ≫ S i) =
        𝟙 _ :=
      (SheafOfModules.toRestrictOverHom_sum.{u} (R := X.sheaf)
        Finset.univ (fun i ↦ C i ≫ S i)).symm.trans
        ((congrArg (SheafOfModules.toRestrictOverHom.{u} (R := X.sheaf)) htot).trans
          (SheafOfModules.toRestrictOverHom_id M))
    rw [← PresheafOfModules.restrictOverMap_sum, hU]
    rfl
  let q := PresheafOfModules.homObjEvalId M.val (PresheafOfModules.unit _) V
  exact ⟨LinearEquiv.ofBijective q (evaluation_bijective_of_generators X M V I s t htotal),
    fun _ _ ↦ rfl⟩

end AlgebraicGeometry.Scheme.Modules
