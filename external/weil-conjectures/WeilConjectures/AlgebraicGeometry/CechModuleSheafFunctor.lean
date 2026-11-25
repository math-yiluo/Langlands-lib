/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf

/-! # The module sheaf of sections on intersections

Source: blueprint `lemma-coherent-base-change-invertible-sheaves`, proof paragraph 1.
(blueprint: def-pc-cech-module-sheaf-functor).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Sections on intersections, constructed by restriction to the over site and its
right adjoint. Its sections on V are F(W × V), with scalars restricted along prod.snd.
(blueprint: def-pc-cech-module-sheaf-functor) -/
noncomputable def cechIntersectionSheaf {X : Scheme.{u}} (F : X.Modules)
    (W : X.Opens) : X.Modules :=
  (SheafOfModules.pushforward (SheafOfModules.pushforwardOver W)).obj (F.over W)

set_option backward.isDefEq.respectTransparency false in
/-- Restrict the first variable of the intersection sheaf. -/
noncomputable def cechIntersectionSheafMap {X : Scheme.{u}} (F : X.Modules)
    {W Z : X.Opens} (f : W ⟶ Z) :
    cechIntersectionSheaf F Z ⟶ cechIntersectionSheaf F W where
  val.app V := ModuleCat.ofHom
    (X := (cechIntersectionSheaf F Z).val.obj V)
    (Y := (cechIntersectionSheaf F W).val.obj V)
    { toFun := F.val.map (prod.map f (𝟙 V.unop)).op
      map_add' := map_add _
      map_smul' r x := by
        have hr : X.ringCatSheaf.obj.map (prod.map f (𝟙 V.unop)).op
            (X.ringCatSheaf.obj.map (prod.snd : Z ⨯ V.unop ⟶ V.unop).op r) =
            X.ringCatSheaf.obj.map (prod.snd : W ⨯ V.unop ⟶ V.unop).op r := by
          rw [← RingCat.comp_apply, ← Functor.map_comp, ← op_comp]
          congr 2
        have h := F.val.map_smul (prod.map f (𝟙 V.unop)).op
          (X.ringCatSheaf.obj.map (prod.snd : Z ⨯ V.unop ⟶ V.unop).op r)
          (x : F.val.obj (op (Z ⨯ V.unop)))
        rw [hr] at h
        exact h }
  val.naturality {V T} g := by
    ext x
    change F.val.map (prod.map f (𝟙 T.unop)).op
        (F.val.map (prod.map (𝟙 Z) g.unop).op x) =
      F.val.map (prod.map (𝟙 W) g.unop).op
        (F.val.map (prod.map f (𝟙 V.unop)).op x)
    simp only [← F.val.map_comp_apply, ← op_comp]
    congr 2

/-- The genuine opposite-opens functor used to form the module-sheaf Čech complex.
Identity and composition are the identities for restriction maps of F.
(blueprint: def-pc-cech-module-sheaf-functor) -/
noncomputable def cechModuleSheafFunctor {X : Scheme.{u}} (F : X.Modules) :
    X.Opensᵒᵖ ⥤ X.Modules where
  obj W := cechIntersectionSheaf F W.unop
  map f := cechIntersectionSheafMap F f.unop
  map_id W := by
    apply SheafOfModules.hom_ext
    ext V x
    change F.val.map (prod.map (𝟙 W.unop) (𝟙 V.unop)).op x = x
    rw [show prod.map (𝟙 W.unop) (𝟙 V.unop) = 𝟙 _ from Subsingleton.elim _ _]
    exact ConcreteCategory.congr_hom (F.val.presheaf.map_id _) x
  map_comp f g := by
    apply SheafOfModules.hom_ext
    ext V x
    change F.val.map (prod.map (g.unop ≫ f.unop) (𝟙 V.unop)).op x =
      F.val.map (prod.map g.unop (𝟙 V.unop)).op
        (F.val.map (prod.map f.unop (𝟙 V.unop)).op x)
    rw [← F.val.map_comp_apply, ← op_comp]
    congr 2

/-- The restriction map to an intersection sheaf, from the over-site adjunction. -/
noncomputable def cechIntersectionRestriction {X : Scheme.{u}} (F : X.Modules)
    (W : X.Opens) : F ⟶ cechIntersectionSheaf F W :=
  (SheafOfModules.overPushforwardOverAdj W).unit.app F

/-- The restriction maps are natural in the first intersection variable. -/
theorem cechIntersectionRestriction_naturality {X : Scheme.{u}} (F : X.Modules)
    {W Z : X.Opens} (f : W ⟶ Z) :
    cechIntersectionRestriction F Z ≫ cechIntersectionSheafMap F f =
      cechIntersectionRestriction F W := by
  apply SheafOfModules.hom_ext
  ext V x
  change F.val.map (prod.map f (𝟙 V.unop)).op (F.val.map prod.snd.op x) =
    F.val.map prod.snd.op x
  rw [← F.val.map_comp_apply, ← op_comp]
  congr 2

/-- The actual full Čech complex of module sheaves; no existence witness is chosen. -/
noncomputable def cechModuleSheafComplex {X : Scheme.{u}} {ι : Type u}
    (U : ι → X.Opens) (F : X.Modules) : CochainComplex X.Modules ℕ :=
  (cechComplexFunctor U).obj (cechModuleSheafFunctor F)

/-- The product of restriction maps in degree zero. -/
noncomputable def cechModuleSheafAugmentation₀ {X : Scheme.{u}} {ι : Type u}
    (U : ι → X.Opens) (F : X.Modules) : F ⟶ (cechModuleSheafComplex U F).X 0 :=
  Pi.lift fun y : Fin 1 → ι => cechIntersectionRestriction F (∏ᶜ fun l => U (y l))

/-- The two cofaces of the degree-zero restriction map agree. -/
private theorem cechModuleSheafAugmentation₀_coface {X : Scheme.{u}} {ι : Type u}
    (U : ι → X.Opens) (F : X.Modules) (i : Fin 2) :
    cechModuleSheafAugmentation₀ U F ≫
      ((FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk _ U).cech).obj
        (cechModuleSheafFunctor F)).δ i =
      Pi.lift (fun y : Fin 2 → ι =>
        cechIntersectionRestriction F (∏ᶜ fun l => U (y l))) := by
  apply Pi.hom_ext
  intro y
  simp only [cechModuleSheafAugmentation₀, FormalCoproduct.cosimplicialObjectFunctor,
    FormalCoproduct.evalOp, FormalCoproduct.cech, FormalCoproduct.mapPower, FormalCoproduct.power,
    CosimplicialObject.δ, Functor.comp_obj, Functor.comp_map,
    Functor.whiskeringLeft_obj_obj, Functor.rightOp_map, Functor.rightOp_obj,
    Category.assoc, Pi.lift_comp_π, Pi.lift_comp_π_assoc, cechModuleSheafFunctor, Function.comp_def]
  exact cechIntersectionRestriction_naturality F _

set_option backward.isDefEq.respectTransparency false in
/-- The product of restrictions is killed by the first Čech differential. The two
cofaces have identical composites, so their alternating difference is zero. -/
theorem cechModuleSheafAugmentation₀_comp_d {X : Scheme.{u}} {ι : Type u}
    (U : ι → X.Opens) (F : X.Modules) :
    cechModuleSheafAugmentation₀ U F ≫ (cechModuleSheafComplex U F).d 0 1 = 0 := by
  change cechModuleSheafAugmentation₀ U F ≫
    AlgebraicTopology.AlternatingCofaceMapComplex.objD
      ((FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk _ U).cech).obj
        (cechModuleSheafFunctor F)) 0 = 0
  rw [AlgebraicTopology.AlternatingCofaceMapComplex.objD, Fin.sum_univ_two]
  simp only [
    Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one,
    neg_smul, Preadditive.comp_add, Preadditive.comp_neg,
    cechModuleSheafAugmentation₀_coface, add_neg_cancel]

end AlgebraicGeometry
