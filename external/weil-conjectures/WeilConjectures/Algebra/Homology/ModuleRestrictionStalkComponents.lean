/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import Mathlib.Topology.Sheaves.Module
public import Mathlib.Geometry.RingedSpace.Stalks

@[expose] public section
open CategoryTheory TopologicalSpace Opposite
universe u
noncomputable section
namespace AlgebraicGeometry

-- Check scalar compatibility on germs over one common neighborhood.  Keeping the
-- presheaf abstract avoids unfolding restriction and colimit module structures here.
private theorem stalkMap_smul_of_germ_smul {Y : TopCat.{u}}
    {R : Y.Presheaf CommRingCat.{u}} (M : PresheafOfModules.{u} (R ⋙ forget₂ _ _))
    (y : Y) {S : Type u} [CommRing S] {P : Type u} [AddCommGroup P] [Module S P]
    (f : R.stalk y →+* S) (a : TopCat.Presheaf.stalk (C := Ab.{u}) (X := Y) M.presheaf y →+ P)
    (h : ∀ (V : Opens Y) (hy : y ∈ V) (r : R.obj (op V)) (m : M.obj (op V)),
      a (TopCat.Presheaf.germ M.presheaf V y hy (r • m)) =
        f (R.germ V y hy r) • a (TopCat.Presheaf.germ M.presheaf V y hy m))
    (r : R.stalk y) (m : TopCat.Presheaf.stalk (C := Ab.{u}) (X := Y) M.presheaf y) :
    a (r • m) = f r • a m := by
  obtain ⟨U, hyU, r, rfl⟩ := R.exists_germ_eq r
  obtain ⟨V, hyV, m, rfl⟩ := TopCat.Presheaf.exists_germ_eq M.presheaf m
  have hy : y ∈ U ⊓ V := ⟨hyU, hyV⟩
  rw [← R.germ_res_apply (homOfLE inf_le_left : U ⊓ V ⟶ U) y hy r,
    ← TopCat.Presheaf.germ_res_apply M.presheaf
      (homOfLE inf_le_right : U ⊓ V ⟶ V) y hy m,
    ← PresheafOfModules.germ_smul (R := R) M]
  exact h (U ⊓ V) hy _ _

-- Build the transported linear map with abstract modules, so checking linearity
-- does not unfold the stalk module instances.
private def restrictScalarsHomOfSemilinear {R S : CommRingCat.{u}} (e : R ≅ S)
    (M : ModuleCat.{u} R) (P : ModuleCat.{u} S) (a : M →+ P)
    (h : ∀ (r : R) (m : M), a (r • m) = e.hom r • a m) :
    (ModuleCat.restrictScalars e.inv.hom).obj M ⟶ P :=
  ModuleCat.ofHom
    (X := (ModuleCat.restrictScalars e.inv.hom).obj M) (Y := P)
    { toFun := a
      map_add' := a.map_add
      map_smul' := fun r m ↦ by
        change a (e.inv r • m) = r • a m
        exact (h (e.inv r) m).trans
          (congrArg (fun t : S ↦ t • a m) (e.inv_hom_id_apply r)) }

-- Comparing stalk module structures through restriction unfolds nested colimit instances.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Componentwise linear stalk comparison for restriction, with its germ formula.
Source: Stacks Project, Sheaves Section 6.31, Lemma 6.31.1 (3).
(blueprint: new-module-restriction-stalk-components).

Proof: represent a restricted stalk element by a germ on a neighborhood in the open,
then send it to the germ on its image in the ambient space.  The additive stalk
comparison is induced by the final neighborhood functor.  The germ scalar
multiplication formula, applied on a common neighborhood, shows that this map is
linear after transporting scalars along the inverse restriction-stalk ring map.
-/
theorem exists_moduleRestrictionStalk_components (X : RingedSpace.{u}) (W : Opens X)
    (x : X) (hx : x ∈ W) :
    ∃ c : ∀ F : SheafOfModules.{u} (moduleRings X),
      (ModuleCat.restrictScalars
          (X.toPresheafedSpace.restrictStalkIso W.isOpenEmbedding ⟨x, hx⟩).inv.hom).obj
        ((RingedSpace.moduleStalkFunctor (X.restrict W.isOpenEmbedding) ⟨x, hx⟩).obj
          ((W.sheafOfModulesEquivOver (moduleRings X)).functor.obj
            ((SheafOfModules.overFunctor (moduleRings X) W).obj F))) ⟶
        (RingedSpace.moduleStalkFunctor X x).obj F,
      ∀ (F : SheafOfModules.{u} (moduleRings X)) (V : Opens W)
        (hV : (⟨x, hx⟩ : W) ∈ V)
        (s : F.val.obj (op (W.isOpenEmbedding.isOpenMap.functor.obj V))),
        (c F) (TopCat.Presheaf.germ (C := Ab.{u})
          (X := (X.restrict W.isOpenEmbedding).carrier)
          ((W.sheafOfModulesEquivOver (moduleRings X)).functor.obj
            ((SheafOfModules.overFunctor (moduleRings X) W).obj F)).val.presheaf
          V ⟨x, hx⟩ hV s) =
        TopCat.Presheaf.germ (C := Ab.{u}) (X := X.carrier) F.val.presheaf
          (W.isOpenEmbedding.isOpenMap.functor.obj V) x ⟨⟨x, hx⟩, hV, rfl⟩ s := by
  classical
  let y : W := ⟨x, hx⟩
  let Y : RingedSpace.{u} := X.restrict W.isOpenEmbedding
  let eR : Y.presheaf.stalk y ≅ X.presheaf.stalk x :=
    X.toPresheafedSpace.restrictStalkIso W.isOpenEmbedding y
  let N (F : SheafOfModules.{u} (moduleRings X)) : RingedSpace.Modules Y :=
    (W.sheafOfModulesEquivOver (moduleRings X)).functor.obj
      ((SheafOfModules.overFunctor (moduleRings X) W).obj F)
  let C (F : SheafOfModules.{u} (moduleRings X)) :
      Limits.Cocone ((OpenNhds.inclusion y).op ⋙ (N F).val.presheaf) :=
    { pt := TopCat.Presheaf.stalk (C := Ab.{u}) (X := X.carrier) F.val.presheaf x
      ι :=
        { app := fun (V : (OpenNhds y)ᵒᵖ) ↦ AddCommGrpCat.ofHom <|
            AddMonoidHom.mk'
              (fun s ↦ TopCat.Presheaf.germ (C := Ab.{u}) (X := X.carrier)
                F.val.presheaf (W.isOpenEmbedding.isOpenMap.functor.obj V.unop.1)
                x ⟨y, V.unop.2, rfl⟩ s)
              (fun s t ↦ map_add _ s t)
          naturality := by
            intro U V f
            ext s
            change TopCat.Presheaf.germ (C := Ab.{u}) (X := X.carrier)
              F.val.presheaf _ x _
                (F.val.presheaf.map (W.isOpenEmbedding.isOpenMap.functor.map
                  (homOfLE f.unop.le : V.unop.1 ⟶ U.unop.1)).op s) = _
            exact TopCat.Presheaf.germ_res_apply (C := Ab.{u}) (X := X.carrier)
              F.val.presheaf
              (W.isOpenEmbedding.isOpenMap.functor.map
                (homOfLE f.unop.le : V.unop.1 ⟶ U.unop.1)) x ⟨y, V.unop.2, rfl⟩ s } }
  let a (F : SheafOfModules.{u} (moduleRings X)) :
      TopCat.Presheaf.stalk (C := Ab.{u}) (X := Y.carrier) (N F).val.presheaf y ⟶
        TopCat.Presheaf.stalk (C := Ab.{u}) (X := X.carrier) F.val.presheaf x :=
    Limits.colimit.desc _ (C F)
  have hg (F : SheafOfModules.{u} (moduleRings X)) (V : Opens W) (hV : y ∈ V)
      (s : F.val.obj (op (W.isOpenEmbedding.isOpenMap.functor.obj V))) :
      a F (TopCat.Presheaf.germ (C := Ab.{u}) (X := Y.carrier)
        (N F).val.presheaf V y hV s) =
        TopCat.Presheaf.germ (C := Ab.{u}) (X := X.carrier) F.val.presheaf
          (W.isOpenEmbedding.isOpenMap.functor.obj V) x ⟨y, hV, rfl⟩ s := by
    exact ConcreteCategory.congr_hom (Limits.colimit.ι_desc (C F) (op ⟨V, hV⟩)) s
  have hs (F : SheafOfModules.{u} (moduleRings X))
      (r : Y.presheaf.stalk y)
      (m : TopCat.Presheaf.stalk (C := Ab.{u}) (X := Y.carrier) (N F).val.presheaf y) :
      a F (r • m) = eR.hom r • a F m := by
    apply stalkMap_smul_of_germ_smul (R := Y.presheaf) (N F).val y eR.hom.hom (a F).hom
    intro V hy r m
    rw [hg F V hy, hg F V hy]
    have hr := X.toPresheafedSpace.restrictStalkIso_hom_eq_germ_apply
      W.isOpenEmbedding V y hy r
    exact (PresheafOfModules.germ_smul (R := X.presheaf) F.val x
      (W.isOpenEmbedding.isOpenMap.functor.obj V) ⟨y, hy, rfl⟩ r m).trans
        (congrArg (fun t : X.presheaf.stalk x ↦ t •
          TopCat.Presheaf.germ (C := Ab.{u}) (X := X.carrier) F.val.presheaf
            (W.isOpenEmbedding.isOpenMap.functor.obj V) x ⟨y, hy, rfl⟩ m) hr.symm)
  let c (F : SheafOfModules.{u} (moduleRings X)) :
      (ModuleCat.restrictScalars eR.inv.hom).obj
          ((RingedSpace.moduleStalkFunctor Y y).obj (N F)) ⟶
        (RingedSpace.moduleStalkFunctor X x).obj F :=
    restrictScalarsHomOfSemilinear eR
      ((RingedSpace.moduleStalkFunctor Y y).obj (N F))
      ((RingedSpace.moduleStalkFunctor X x).obj F) (a F).hom (hs F)
  refine ⟨c, ?_⟩
  intro F V hV s
  exact hg F V hV s

end AlgebraicGeometry
end
