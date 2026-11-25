/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedBaseChangeUnitCompatibility

/-! # Ordinary exchange on homotopy single complexes

Source: Stacks Project, Tag 08HY; functoriality of the homotopy quotient.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules

-- Degree-zero simplification unfolds the single-complex construction.
private theorem single_exchange
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Preadditive A] [Preadditive B] [Preadditive C] [Preadditive D]
    [Limits.HasZeroObject A] [Limits.HasZeroObject B]
    [Limits.HasZeroObject C] [Limits.HasZeroObject D]
    (F : A ⥤ B) (G : B ⥤ D) (H : A ⥤ C) (I : C ⥤ D)
    [F.Additive] [G.Additive] [H.Additive] [I.Additive]
    (α : F ⋙ G ⟶ H ⋙ I) (M : A) (N : C) (z : H.obj M ⟶ N) :
    (G.mapHomologicalComplex (.up ℤ)).map
      ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).inv.app M) ≫
    (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).hom.app
      ((HomologicalComplex.single A (.up ℤ) 0).obj M) ≫
    (NatTrans.mapHomologicalComplex α (.up ℤ)).app
      ((HomologicalComplex.single A (.up ℤ) 0).obj M) ≫
    (Functor.mapHomologicalComplexCompIso (Iso.refl (H ⋙ I)) (.up ℤ)).inv.app
      ((HomologicalComplex.single A (.up ℤ) 0).obj M) ≫
    (I.mapHomologicalComplex (.up ℤ)).map
      ((HomologicalComplex.singleMapHomologicalComplex H (.up ℤ) 0).hom.app M ≫
        (HomologicalComplex.single C (.up ℤ) 0).map z) =
  (HomologicalComplex.singleMapHomologicalComplex G (.up ℤ) 0).hom.app (F.obj M) ≫
    (HomologicalComplex.single D (.up ℤ) 0).map (α.app M ≫ I.map z) ≫
    (HomologicalComplex.singleMapHomologicalComplex I (.up ℤ) 0).inv.app
      N := by
  rw [← cancel_mono
    ((HomologicalComplex.singleMapHomologicalComplex I (.up ℤ) 0).hom.app
      N)]
  apply HomologicalComplex.to_single_hom_ext
  simp [HomologicalComplex.singleMapHomologicalComplex, HomologicalComplex.single,
    Functor.mapHomologicalComplexCompIso, NatIso.mapHomologicalComplex,
    NatTrans.mapHomologicalComplex, Functor.mapHomologicalComplex]

private theorem single_homotopy_exchange
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Preadditive A] [Preadditive B] [Preadditive C] [Preadditive D]
    [Limits.HasZeroObject A] [Limits.HasZeroObject B]
    [Limits.HasZeroObject C] [Limits.HasZeroObject D]
    (F : A ⥤ B) (G : B ⥤ D) (H : A ⥤ C) (I : C ⥤ D)
    [F.Additive] [G.Additive] [H.Additive] [I.Additive]
    (α : F ⋙ G ⟶ H ⋙ I) (M : A) (N : C) (z : H.obj M ⟶ N) :
    (G.mapHomotopyCategory (.up ℤ)).map
      ((HomotopyCategory.quotient B (.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).inv.app M)) ≫
    (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).hom.app
      ((HomotopyCategory.singleFunctor A 0).obj M) ≫
    (NatTrans.mapHomotopyCategory α (.up ℤ)).app
      ((HomotopyCategory.singleFunctor A 0).obj M) ≫
    (Functor.mapHomotopyCategoryCompIso (Iso.refl (H ⋙ I)) (.up ℤ)).inv.app
      ((HomotopyCategory.singleFunctor A 0).obj M) ≫
    (I.mapHomotopyCategory (.up ℤ)).map
      ((HomotopyCategory.quotient C (.up ℤ)).map
          ((HomologicalComplex.singleMapHomologicalComplex H (.up ℤ) 0).hom.app M) ≫
        (HomotopyCategory.singleFunctor C 0).map z) =
    (HomotopyCategory.quotient D (.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex G (.up ℤ) 0).hom.app (F.obj M)) ≫
      (HomotopyCategory.singleFunctor D 0).map (α.app M ≫ I.map z) ≫
      (HomotopyCategory.quotient D (.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex I (.up ℤ) 0).inv.app N) := by
  have hc := single_exchange F G H I α M N z
  have hq := congrArg (fun t ↦ (HomotopyCategory.quotient D (.up ℤ)).map t) hc
  simpa only [Functor.map_comp, Functor.mapHomotopyCategory_map,
    HomotopyCategory.singleFunctor, HomotopyCategory.singleFunctors,
    SingleFunctors.postcomp, CochainComplex.singleFunctors, Functor.comp_map,
    Functor.comp_obj, Functor.mapHomotopyCategoryCompIso,
    Quotient.natIsoLift_hom, Quotient.natIsoLift_inv, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerRight_inv, Quotient.natTransLift, NatTrans.mapHomotopyCategory,
    Functor.whiskerRight_app, HomotopyCategory.quotient_obj_as,
    NatTrans.comp_app, Category.assoc] using hq

/-- The ordinary exchange intertwines the termwise single-object identifications.
Source: Stacks Project, Tag 08HY, ordinary mate construction.
(blueprint: lem-sc-homotopy-single-base-change-comparison).

Proof: Form the natural transformation of module functors whose components are
moduleBaseChangeMap. Apply the functors to single complexes. Postcompose both
candidate chain maps with the single-map isomorphism for f' pushforward. A map to
a single complex is determined in degree zero. In that degree all single-map and
composition identifications are identities, so both maps are the ordinary
exchange followed by pushforward of the tensor-to-ordinary p-pullback comparison.
Cancel the postcomposed isomorphism. Apply the homotopy quotient, using its
functoriality and the defining quotient lifts for termwise functors and their
composition comparisons. This gives the displayed equation. No comparison of
an unbounded derived functor is involved. Zero modules and empty schemes satisfy
the same degree-zero calculation. -/
theorem homotopySingleBaseChangeComparison
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (p : X' ⟶ X)
    (h : p ≫ f = f' ≫ g) (M : X.Modules)
    [(tensorPullback g).Additive] [(tensorPullback p).Additive] :
  let C_X := SheafOfModules.{u} (moduleRings X.toRingedSpace)
  let C_S := SheafOfModules.{u} (moduleRings S.toRingedSpace)
  let C_X' := SheafOfModules.{u} (moduleRings X'.toRingedSpace)
  let C_S' := SheafOfModules.{u} (moduleRings S'.toRingedSpace)
  let E := (HomotopyCategory.singleFunctor C_X 0).obj M
  let F : C_X ⥤
      C_S :=
    RingedSpace.moduleDirectImage f.toLRSHom.toShHom
  let G : C_S ⥤
      C_S' := tensorPullback g
  let H : C_X ⥤
      C_X' := tensorPullback p
  let I : C_X' ⥤
      C_S' :=
    RingedSpace.moduleDirectImage f'.toLRSHom.toShHom
  let _ : F.Additive := RingedSpace.moduleDirectImage_additive f.toLRSHom.toShHom
  let _ : I.Additive := RingedSpace.moduleDirectImage_additive f'.toLRSHom.toShHom
  let t_p := (Classical.choose (exists_tensorPullbackAdjunction p)).leftAdjointUniq
    (pullbackPushforwardAdjunction p)
  let a := (HomotopyCategory.quotient C_S (.up ℤ)).map
    ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).inv.app M)
  let b := (HomotopyCategory.quotient C_X' (.up ℤ)).map
      ((HomologicalComplex.singleMapHomologicalComplex H (.up ℤ) 0).hom.app M) ≫
    (HomotopyCategory.singleFunctor C_X' 0).map (t_p.hom.app M)
  let c := (HomotopyCategory.quotient C_S' (.up ℤ)).map
    ((HomologicalComplex.singleMapHomologicalComplex G (.up ℤ) 0).hom.app (F.obj M))
  let d := (HomotopyCategory.quotient C_S' (.up ℤ)).map
    ((HomologicalComplex.singleMapHomologicalComplex I (.up ℤ) 0).inv.app
      ((pullback p).obj M))
  let k := moduleBaseChangeMap f f' g p h M ≫ I.map (t_p.hom.app M)
  (G.mapHomotopyCategory (.up ℤ)).map a ≫
      (moduleHomotopyBaseChange f f' g p h).app E ≫
      (I.mapHomotopyCategory (.up ℤ)).map b =
    c ≫ (HomotopyCategory.singleFunctor C_S' 0).map k ≫ d := by
  let C_X := SheafOfModules.{u} (moduleRings X.toRingedSpace)
  let C_S := SheafOfModules.{u} (moduleRings S.toRingedSpace)
  let C_X' := SheafOfModules.{u} (moduleRings X'.toRingedSpace)
  let C_S' := SheafOfModules.{u} (moduleRings S'.toRingedSpace)
  let E := (HomotopyCategory.singleFunctor C_X 0).obj M
  let F := RingedSpace.moduleDirectImage f.toLRSHom.toShHom
  let G := tensorPullback g
  let H := tensorPullback p
  let I := RingedSpace.moduleDirectImage f'.toLRSHom.toShHom
  have : F.Additive := RingedSpace.moduleDirectImage_additive f.toLRSHom.toShHom
  have : I.Additive := RingedSpace.moduleDirectImage_additive f'.toLRSHom.toShHom
  let t_p := (Classical.choose (exists_tensorPullbackAdjunction p)).leftAdjointUniq
    (pullbackPushforwardAdjunction p)
  let α : F ⋙ G ⟶ H ⋙ I :=
    { app := moduleBaseChangeMap f f' g p h
      naturality := fun _ _ z ↦ moduleBaseChangeMap_naturality f f' g p h z }
  dsimp only
  exact single_homotopy_exchange F G H I α M ((pullback p).obj M) (t_p.hom.app M)

end AlgebraicGeometry.Scheme.Modules
