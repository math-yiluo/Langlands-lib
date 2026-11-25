/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectHomTransport
public import WeilConjectures.Algebra.Homology.ScalarExtensionHom
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.AlgebraicGeometry.Modules.Tilde

/-! # Coherent comparison data for affine complex models
Source: Stacks Project, Tags 09RE and 08DW, affine comparison formula.
(blueprint: def-pc-affine-model-comparison-data). -/

@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The explicit proposition of coherent scheme transports and model isomorphisms.
Its data are the derived equivalences, the four families of object isomorphisms,
and the two sheafified-chain-map compatibility equations written below. This is
notation for that formula, not data chosen from an existence theorem.
Source: Stacks Project, Tags 09RE and 08DW, affine comparison formula.
(blueprint: def-pc-affine-model-comparison-data). -/
@[irreducible]
def affineModelComparisonData
    {I : Type u} [Preorder I]
    (R : I ⥤ CommRingCat.{u}) (c : Cocone R)
    (i : I) (Y : Scheme.{u}) [IsAffine Y] (s : Y ⟶ Spec (R.obj i))
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    (P Q : schemeDerivedCategory Y)
    (F : Set.Ici i ⥤ CommRingCat.{u}) (C : Cocone F)
    (E K : CochainComplex (ModuleCat.{u} (F.obj ⟨i, le_rfl⟩)) ℤ)
    : Prop :=
    let T (A : CommRingCat.{u}) :=
      @Functor.mapHomologicalComplex ℤ (ModuleCat.{u} A)
        (SheafOfModules.{u} (moduleRings (Spec A).toRingedSpace))
        _ _ _ _ (@id (ModuleCat.{u} A ⥤
          SheafOfModules.{u} (moduleRings (Spec A).toRingedSpace)) (tilde.functor A))
        ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)
    ∃ (d : ∀ j : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i),
          schemeDerivedCategory (Spec (F.obj j.val)) ≌
            schemeDerivedCategory (pullback s (Spec.map (R.map (homOfLE j.val.property)))))
      (dlim : schemeDerivedCategory (Spec (C.pt)) ≌
        schemeDerivedCategory (pullback s (Spec.map (c.ι.app i))))
      (αE : ∀ j : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i),
          (d j).functor.obj (DerivedCategory.Q.obj
            ((T (F.obj j.val)).obj ((Functor.mapHomologicalComplex
              (ModuleCat.extendScalars (F.map (homOfLE j.property)).hom) (.up ℤ)).obj E))) ≅
          (derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE j.val.property))))).obj P)
      (αK : ∀ j : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i),
          (d j).functor.obj (DerivedCategory.Q.obj
            ((T (F.obj j.val)).obj ((Functor.mapHomologicalComplex
              (ModuleCat.extendScalars (F.map (homOfLE j.property)).hom) (.up ℤ)).obj K))) ≅
          (derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE j.val.property))))).obj Q)
      (βE : dlim.functor.obj (DerivedCategory.Q.obj
            ((T (C.pt : CommRingCat.{u})).obj ((Functor.mapHomologicalComplex
              (ModuleCat.extendScalars (C.ι.app ⟨i, le_rfl⟩).hom) (.up ℤ)).obj E))) ≅
          (derivedPullback (pullback.fst s (Spec.map (c.ι.app i)))).obj P)
      (βK : dlim.functor.obj (DerivedCategory.Q.obj
            ((T (C.pt : CommRingCat.{u})).obj ((Functor.mapHomologicalComplex
              (ModuleCat.extendScalars (C.ι.app ⟨i, le_rfl⟩).hom) (.up ℤ)).obj K))) ≅
          (derivedPullback (pullback.fst s (Spec.map (c.ι.app i)))).obj Q),
      (∀ (j k : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i)) (hjk : j ≤ k)
          (f : ((Functor.mapHomologicalComplex
              (ModuleCat.extendScalars (F.map (homOfLE j.property)).hom) (.up ℤ)).obj E) ⟶
            ((Functor.mapHomologicalComplex
              (ModuleCat.extendScalars (F.map (homOfLE j.property)).hom) (.up ℤ)).obj K)),
        (αE k).inv ≫ (d k).functor.map (DerivedCategory.Q.map
              ((T (F.obj k.val)).map (CochainComplex.scalarExtensionHom
                (F.map (homOfLE j.property)).hom (F.map (homOfLE hjk)).hom
                (F.map (homOfLE k.property)).hom
                (congrArg CommRingCat.Hom.hom (F.map_comp
                  (homOfLE j.property) (homOfLE hjk))) E K f))) ≫ (αK k).hom =
          perfectStageMap R s j.val.property hjk
            ((αE j).inv ≫ (d j).functor.map (DerivedCategory.Q.map
              ((T (F.obj j.val)).map (f))) ≫ (αK j).hom)) ∧
      (∀ (j : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i))
          (f : ((Functor.mapHomologicalComplex
              (ModuleCat.extendScalars (F.map (homOfLE j.property)).hom) (.up ℤ)).obj E) ⟶
            ((Functor.mapHomologicalComplex
              (ModuleCat.extendScalars (F.map (homOfLE j.property)).hom) (.up ℤ)).obj K)),
        βE.inv ≫ dlim.functor.map (DerivedCategory.Q.map
              ((T (C.pt : CommRingCat.{u})).map (CochainComplex.scalarExtensionHom
                (F.map (homOfLE j.property)).hom (C.ι.app j.val).hom
                (C.ι.app ⟨i, le_rfl⟩).hom
                (congrArg CommRingCat.Hom.hom (C.w (homOfLE j.property)).symm)
                E K f))) ≫ βK.hom =
          perfectLimitMap R c s j.val.property
            ((αE j).inv ≫ (d j).functor.map (DerivedCategory.Q.map
              ((T (F.obj j.val)).map (f))) ≫ (αK j).hom))

end AlgebraicGeometry
