/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Stalk
import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
import WeilConjectures.Algebra.Homology.ModuleExtensionByZeroUnitIsIso

/-!
# Stalks of the extension by zero at points of the open

## References

* [Stacks: Tag 00A7](https://stacks.math.columbia.edu/tag/00A7)
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
/-- For a point `x` of the open `U`, the unit of the extension-by-zero adjunction induces an
isomorphism from the stalk of a sheaf `F` on `U` at `x` to the stalk of its extension by zero,
linear over the stalk of the structure sheaf and natural in `F`. -/
theorem module_extensionByZero_inside_stalk (X : Scheme.{u}) (U : X.Opens) :
    let R := X.ringCatSheaf
    let P := SheafOfModules.extensionByZeroPresheaf.{u} R U
    let L := P ⋙ PresheafOfModules.sheafification (𝟙 R.obj)
    ∀ adj : L ⊣ SheafOfModules.overFunctor R U,
      let t : ∀ (F : SheafOfModules.{u} (R.over U)) (x : U),
          (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj
              ((toPresheaf U.toScheme).obj ((overEquiv U).functor.obj F)) ⟶
            (toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u}
              (U.ι x)).obj (L.obj F) := fun F x =>
        (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
            ((toPresheaf U.toScheme).map ((overEquiv U).functor.map (adj.unit.app F) ≫
              (overFunctorEquiv U).hom.app (L.obj F))) ≫
          (restrictStalkNatIso U.ι x).hom.app (L.obj F)
      (∀ (F : SheafOfModules.{u} (R.over U)) (x : U),
        letI : Module (U.toScheme.presheaf.stalk x)
            (((overEquiv U).functor.obj F).presheaf.stalk x) :=
          inferInstanceAs (Module (U.toScheme.presheaf.stalk x)
          ↑(TopCat.Presheaf.stalk ((overEquiv U).functor.obj F).val.presheaf x))
        letI : Module (X.presheaf.stalk (U.ι x))
            ((toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u}
              (U.ι x)).obj (L.obj F)) :=
          inferInstanceAs (Module (X.presheaf.stalk (U.ι x))
          ↑(TopCat.Presheaf.stalk (L.obj F).val.presheaf (U.ι x)))
        IsIso (t F x) ∧
          ∀ (r : X.presheaf.stalk (U.ι x))
            (s : ((overEquiv U).functor.obj F).presheaf.stalk x),
            t F x ((U.ι.stalkMap x) r • s) = r • t F x s) ∧
      (∀ (F F' : SheafOfModules.{u} (R.over U)) (α : F ⟶ F') (x : U),
        t F x ≫ (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (U.ι x)).map
            ((toPresheaf X).map (L.map α)) =
          (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
            ((toPresheaf U.toScheme).map ((overEquiv U).functor.map α)) ≫ t F' x) := by
  dsimp only
  intro adj
  refine ⟨?_, ?_⟩
  · intro F x
    constructor
    · classical
      let a := Classical.choice (open_restriction_adjunction_exact X.toRingedSpace U).2.2.2.2
      have hi (G : SheafOfModules.{u} (X.ringCatSheaf.over U)) : IsIso (a.unit.app G) :=
        moduleExtensionByZero_unit_isIso X.toRingedSpace U G
      let : IsIso a.unit := NatIso.isIso_of_isIso_app a.unit
      let e := a.fullyFaithfulLOfIsIsoUnit
      let := e.full
      let := e.faithful
      have : IsIso (adj.unit.app F) := inferInstance
      infer_instance
    · let M : X.Modules := (SheafOfModules.extensionByZeroPresheaf.{u} X.ringCatSheaf U ⋙
        PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj F
      let : Module (U.toScheme.presheaf.stalk x)
          (((overEquiv U).functor.obj F).presheaf.stalk x) :=
        inferInstanceAs (Module (U.toScheme.presheaf.stalk x)
          ↑(TopCat.Presheaf.stalk ((overEquiv U).functor.obj F).val.presheaf x))
      let : Module (U.toScheme.presheaf.stalk x) ((M.restrict U.ι).presheaf.stalk x) :=
        inferInstanceAs (Module (U.toScheme.presheaf.stalk x)
          ↑(TopCat.Presheaf.stalk (M.restrict U.ι).val.presheaf x))
      let : Module (X.presheaf.stalk (U.ι x)) (M.presheaf.stalk (U.ι x)) :=
        inferInstanceAs (Module (X.presheaf.stalk (U.ι x))
          ↑(TopCat.Presheaf.stalk M.val.presheaf (U.ι x)))
      let f := (overEquiv U).functor.map (adj.unit.app F) ≫ (overFunctorEquiv U).hom.app M
      let c : (M.restrict U.ι).presheaf.stalk x ⟶ M.presheaf.stalk (U.ι x) :=
        (restrictStalkNatIso U.ι x).hom.app M
      have hc (r : U.toScheme.presheaf.stalk x)
          (z : (M.restrict U.ι).presheaf.stalk x) :
          c (r • z) = (show X.presheaf.stalk (U.ι x) from (U.stalkIso x).hom r) • c z := by
        obtain ⟨V, hV, r, rfl⟩ := U.toScheme.presheaf.exists_germ_eq r
        obtain ⟨W, hW, z, rfl⟩ := TopCat.Presheaf.exists_germ_eq (M.restrict U.ι).presheaf z
        have hx : x ∈ V ⊓ W := ⟨hV, hW⟩
        rw [← U.toScheme.presheaf.germ_res_apply
            (homOfLE inf_le_left : V ⊓ W ⟶ V) x hx r,
          ← TopCat.Presheaf.germ_res_apply (M.restrict U.ι).presheaf
            (homOfLE inf_le_right : V ⊓ W ⟶ W) x hx z]
        erw [← PresheafOfModules.germ_smul (R := U.toScheme.presheaf) (M.restrict U.ι).val]
        dsimp only [c]
        have hg := germ_restrictStalkNatIso_hom_app U.ι x M hx
        have hr := U.germ_stalkIso_hom x hx
        change (restrictStalkNatIso U.ι x).hom.app M
          ((M.restrict U.ι).presheaf.germ _ x hx (_ • _)) = _
        have hgc (v : Γ(M.restrict U.ι, V ⊓ W)) :
            (restrictStalkNatIso U.ι x).hom.app M
              ((M.restrict U.ι).presheaf.germ _ x hx v) =
                M.presheaf.germ (U.ι ''ᵁ (V ⊓ W)) (U.ι x) ⟨x, hx, rfl⟩ v :=
          ConcreteCategory.congr_hom hg v
        have hrc (v : Γ(U.toScheme, V ⊓ W)) :
            (U.stalkIso x).hom (U.toScheme.presheaf.germ _ x hx v) =
              X.presheaf.germ (U.ι ''ᵁ (V ⊓ W)) (U.ι x) ⟨x, hx, rfl⟩ v :=
          ConcreteCategory.congr_hom hr v
        erw [hgc, hrc, hgc]
        erw [← PresheafOfModules.germ_smul (R := X.presheaf) M.val]
        congr 1
        have hs := smul_restrictAppIso_hom_apply U.ι M (V ⊓ W)
          (U.toScheme.presheaf.map (homOfLE inf_le_left).op r)
          ((M.restrict U.ι).presheaf.map (homOfLE inf_le_right).op z)
        rw [U.ι_appIso] at hs
        exact hs
      intro r s
      have hf := RingedSpace.stalkMap_linear U.toScheme.toRingedSpace x f
        (U.ι.stalkMap x r) s
      change c (RingedSpace.stalkAddMap U.toScheme.toRingedSpace x f
        ((U.ι.stalkMap x) r • s)) = r • c (RingedSpace.stalkAddMap
          U.toScheme.toRingedSpace x f s)
      rw [hf, hc]
      rw [← U.stalkIso_inv x]
      have h := ConcreteCategory.congr_hom ((U.stalkIso x).inv_hom_id) r
      exact congrArg (fun a => a • c
        (RingedSpace.stalkAddMap U.toScheme.toRingedSpace x f s)) h
  · intro F F' α x
    let L := SheafOfModules.extensionByZeroPresheaf.{u} X.ringCatSheaf U ⋙
      PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
    let A := toPresheaf U.toScheme ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
    let t := Functor.whiskerRight (Functor.whiskerRight adj.unit (overEquiv U).functor) A ≫
      Functor.whiskerLeft L (Functor.whiskerRight (overFunctorEquiv U).hom A) ≫
      Functor.whiskerLeft L (restrictStalkNatIso U.ι x).hom
    simpa only [t, A, L, Functor.map_comp,
      Category.assoc, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      NatTrans.comp_app, Functor.comp_map, Functor.id_map] using (t.naturality α).symm

end AlgebraicGeometry.Scheme.Modules
