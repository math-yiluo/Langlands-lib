/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization

public import WeilConjectures.AlgebraicGeometry.OpenPinnedSingleDegreeZeroCounitIso

/-! # Single-complex identities for exact restriction and tensor reassociation
Source: Stacks Project, Tags 08DW and 08HY; Mathlib exact single comparison.
(blueprint: lem-pc-open-pinned-single-tensor-restriction-factors). -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory Limits
noncomputable section
namespace AlgebraicGeometry

private lemma exact_single_hom
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} D] (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (M : C) :
    F.mapDerivedCategoryFactorsh.hom.app ((HomotopyCategory.singleFunctor C 0).obj M) ≫
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom.app M)) =
    (F.mapDerivedCategorySingleFunctor 0).hom.app M := by
  change F.mapDerivedCategoryFactorsh.hom.app
      ((HomotopyCategory.quotient C (.up ℤ)).obj
        ((HomologicalComplex.single C (.up ℤ) 0).obj M)) ≫ _ = _
  rw [Functor.mapDerivedCategoryFactorsh_hom_app]
  simp only [Functor.comp_obj, DerivedCategory.Q_obj_single_obj,
    DerivedCategory.quotientCompQhIso, HomologicalComplexUpToQuasiIso.quotientCompQhIso,
    Quotient.lift.isLift, NatIso.ofComponents_hom_app, Iso.refl_hom,
    NatIso.ofComponents_inv_app, Iso.refl_inv, Functor.mapHomotopyCategoryFactors,
    Category.assoc, Functor.mapDerivedCategorySingleFunctor,
    DerivedCategory.singleFunctorIsoCompQ, Functor.isoWhiskerRight_refl,
    Functor.isoWhiskerLeft_refl, Iso.refl_symm, Iso.refl_trans, Iso.trans_hom,
    Functor.isoWhiskerLeft_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
    NatTrans.comp_app, Functor.associator_hom_app, Functor.whiskerLeft_app,
    Functor.associator_inv_app, Functor.whiskerRight_app, NatTrans.id_app,
    Category.comp_id, Category.id_comp]
  erw [F.mapDerivedCategory.map_id, DerivedCategory.Qh.map_id]
  erw [Category.id_comp, Category.id_comp]
  simp only [Category.id_comp]
  have h := DerivedCategory.quotientCompQhIso_hom_naturality
    ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom.app M)
  dsimp [DerivedCategory.quotientCompQhIso,
    HomologicalComplexUpToQuasiIso.quotientCompQhIso] at h
  erw [Category.comp_id, Category.id_comp] at h
  rw [h]
  erw [Category.id_comp]

private lemma complex_single_square
    {C D B E : Type*} [Category C] [Category D] [Category B] [Category E]
    [Abelian C] [Abelian D] [Abelian B] [Abelian E] (F : C ⥤ D) (G : D ⥤ E)
    (R : C ⥤ B) (J : B ⥤ E)
    [F.Additive] [G.Additive] [R.Additive] [J.Additive]
    (e : F ⋙ G ≅ R ⋙ J) (M : C) :
    (G.mapHomologicalComplex (.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom.app M) ≫
      (HomologicalComplex.singleMapHomologicalComplex G (.up ℤ) 0).hom.app (F.obj M) ≫
      (HomologicalComplex.single E (.up ℤ) 0).map (e.hom.app M) =
    (Functor.mapHomologicalComplexCompIso e (.up ℤ)).hom.app
        ((HomologicalComplex.single C (.up ℤ) 0).obj M) ≫
      (J.mapHomologicalComplex (.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex R (.up ℤ) 0).hom.app M) ≫
      (HomologicalComplex.singleMapHomologicalComplex J (.up ℤ) 0).hom.app (R.obj M) := by
  apply HomologicalComplex.hom_ext
  intro i
  by_cases h : i = 0
  · subst i
    simp only [HomologicalComplex.single, Functor.comp_obj, ↓dreduceIte,
      HomologicalComplex.singleMapHomologicalComplex, NatIso.ofComponents_hom_app,
      HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f, ↓reduceDIte,
      eqToHom_refl, Category.comp_id, Category.id_comp,
      Functor.mapHomologicalComplexCompIso, NatIso.mapHomologicalComplex,
      NatTrans.mapHomologicalComplex]
    erw [G.map_id, J.map_id]
    change 𝟙 (G.obj (F.obj M)) ≫ e.hom.app M =
      e.hom.app M ≫ 𝟙 (J.obj (R.obj M))
    erw [Category.id_comp, Category.comp_id]
  · simp [HomologicalComplex.singleMapHomologicalComplex, h]

private lemma homotopy_single_square
    {C D B E : Type*} [Category C] [Category D] [Category B] [Category E]
    [Abelian C] [Abelian D] [Abelian B] [Abelian E] (F : C ⥤ D) (G : D ⥤ E)
    (R : C ⥤ B) (J : B ⥤ E)
    [F.Additive] [G.Additive] [R.Additive] [J.Additive]
    (e : F ⋙ G ≅ R ⋙ J) (M : C) :
    (G.mapHomotopyCategory (.up ℤ)).map
        ((HomotopyCategory.quotient _ (.up ℤ)).map
          ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom.app M)) ≫
      (HomotopyCategory.quotient _ (.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex G (.up ℤ) 0).hom.app (F.obj M)) ≫
      (HomotopyCategory.quotient _ (.up ℤ)).map
        ((HomologicalComplex.single E (.up ℤ) 0).map (e.hom.app M)) =
    ((Functor.mapHomotopyCategoryCompIso e (.up ℤ)) ≪≫
        (Functor.mapHomotopyCategoryCompIso (Iso.refl (R ⋙ J)) (.up ℤ)).symm).hom.app
        ((HomotopyCategory.singleFunctor C 0).obj M) ≫
      (J.mapHomotopyCategory (.up ℤ)).map
        ((HomotopyCategory.quotient _ (.up ℤ)).map
          ((HomologicalComplex.singleMapHomologicalComplex R (.up ℤ) 0).hom.app M)) ≫
      (HomotopyCategory.quotient _ (.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex J (.up ℤ) 0).hom.app (R.obj M)) := by
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc,
    Functor.mapHomotopyCategory_map]
  change (HomotopyCategory.quotient E (.up ℤ)).map
      ((G.mapHomologicalComplex (.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom.app M)) ≫
    (HomotopyCategory.quotient E (.up ℤ)).map
      ((HomologicalComplex.singleMapHomologicalComplex G (.up ℤ) 0).hom.app (F.obj M)) ≫
    (HomotopyCategory.quotient E (.up ℤ)).map
      ((HomologicalComplex.single E (.up ℤ) 0).map (e.hom.app M)) =
    (HomotopyCategory.quotient E (.up ℤ)).map
      ((Functor.mapHomologicalComplexCompIso e (.up ℤ)).hom.app
        ((HomologicalComplex.single C (.up ℤ) 0).obj M)) ≫
    (HomotopyCategory.quotient E (.up ℤ)).map (𝟙 _) ≫
    (HomotopyCategory.quotient E (.up ℤ)).map
      ((J.mapHomologicalComplex (.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex R (.up ℤ) 0).hom.app M)) ≫
    (HomotopyCategory.quotient E (.up ℤ)).map
      ((HomologicalComplex.singleMapHomologicalComplex J (.up ℤ) 0).hom.app (R.obj M))
  simp only [Category.id_comp, ← Functor.map_comp]
  exact congrArg (HomotopyCategory.quotient E (.up ℤ)).map
    (complex_single_square F G R J e M)

private lemma derived_single_square
    {C D B E : Type*} [Category C] [Category D] [Category B] [Category E]
    [Abelian C] [Abelian D] [Abelian B] [Abelian E]
    [HasDerivedCategory.{w} D] [HasDerivedCategory.{w} E]
    (F : C ⥤ D) (G : D ⥤ E) (R : C ⥤ B) (J : B ⥤ E)
    [F.Additive] [G.Additive] [R.Additive] [J.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (e : F ⋙ G ≅ R ⋙ J) (M : C) :
    G.mapDerivedCategory.map (DerivedCategory.Qh.map
        ((HomotopyCategory.quotient _ (.up ℤ)).map
          ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom.app M))) ≫
      (G.mapDerivedCategorySingleFunctor 0).hom.app (F.obj M) ≫
      (DerivedCategory.singleFunctor E 0).map (e.hom.app M) =
    G.mapDerivedCategoryFactorsh.hom.app
        ((F.mapHomotopyCategory (.up ℤ)).obj ((HomotopyCategory.singleFunctor C 0).obj M)) ≫
      DerivedCategory.Qh.map
        ((Functor.mapHomotopyCategoryCompIso e (.up ℤ) ≪≫
          (Functor.mapHomotopyCategoryCompIso (Iso.refl (R ⋙ J)) (.up ℤ)).symm).hom.app
            ((HomotopyCategory.singleFunctor C 0).obj M)) ≫
      DerivedCategory.Qh.map ((J.mapHomotopyCategory (.up ℤ)).map
        ((HomotopyCategory.quotient _ (.up ℤ)).map
          ((HomologicalComplex.singleMapHomologicalComplex R (.up ℤ) 0).hom.app M))) ≫
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex J (.up ℤ) 0).hom.app (R.obj M))) := by
  rw [← exact_single_hom G (F.obj M)]
  have hn := G.mapDerivedCategoryFactorsh.hom.naturality
    ((HomotopyCategory.quotient _ (.up ℤ)).map
      ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom.app M))
  dsimp only [Functor.comp_map] at hn
  rw [← Category.assoc, ← Category.assoc]
  erw [hn]
  simp only [Category.assoc]
  apply congrArg (fun f => G.mapDerivedCategoryFactorsh.hom.app
    ((F.mapHomotopyCategory (.up ℤ)).obj ((HomotopyCategory.singleFunctor C 0).obj M)) ≫ f)
  have h := congrArg DerivedCategory.Qh.map (homotopy_single_square F G R J e M)
  simp only [Functor.map_comp] at h
  dsimp only [DerivedCategory.singleFunctor, DerivedCategory.singleFunctors,
    HomotopyCategory.singleFunctor, HomotopyCategory.singleFunctors,
    CochainComplex.singleFunctor, CochainComplex.singleFunctors,
    SingleFunctors.postcomp, Functor.comp_map, Functor.comp_obj] at h ⊢
  exact h

/-- Termwise identities specializing the homotopy counit square to singles.
Source: Stacks Project, Tags 08DW and 08HY; Mathlib ExactFunctor.
(blueprint: lem-pc-open-pinned-single-tensor-restriction-factors).
Proof: expand mapDerivedCategorySingleFunctor and mapDerivedCategoryFactorsh.
The quotientCompQhIso factors cancel, leaving Qh applied to the quotient of
singleMapHomologicalComplex for exact restriction; this proves the first
identity. For the second expand the target isomorphism and the homotopy
composition comparisons. Naturality of the restriction factorization moves
the mapped tensor single comparison past it. Naturality of the single
comparison for the tensor restriction isomorphism and its compatibility with
composition identify the rest. In degree zero both paths are the same tensor
restriction map; in every other degree the maps are between zero objects.
Apply the homotopy quotient and Qh and reassociate. The identities use only
additive tensor pullback and exact restriction, without any derived counit. -/
private theorem open_pinned_single_tensor_restriction_factors_private
    [∀ Y : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ {Y Z : Scheme.{u}} (k : Y ⟶ Z), (Scheme.Modules.tensorPullback k).Additive]
    {X X' : Scheme.{u}} (k : X' ⟶ X)
    (U : X.Opens) (U' : X'.Opens) (j : U'.toScheme ⟶ U.toScheme)
    (hj : j ≫ U.ι = U'.ι ≫ k) (M : X.Modules) :
    let P := (HomotopyCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj M
    let H := (schemeOpenRestriction X U).obj M
    let qR := (HomotopyCategory.quotient _ (.up ℤ)).map
      ((HomologicalComplex.singleMapHomologicalComplex
        (schemeOpenRestriction X U) (.up ℤ) 0).hom.app M)
    let qk := (HomotopyCategory.quotient _ (.up ℤ)).map
      ((HomologicalComplex.singleMapHomologicalComplex
        (Scheme.Modules.tensorPullback k) (.up ℤ) 0).hom.app M)
    let qj := (HomotopyCategory.quotient _ (.up ℤ)).map
      ((HomologicalComplex.singleMapHomologicalComplex
        (Scheme.Modules.tensorPullback j) (.up ℤ) 0).hom.app H)
    (schemeOpenRestriction X U).mapDerivedCategoryFactorsh.hom.app P ≫
        DerivedCategory.Qh.map qR =
      ((schemeOpenRestriction X U).mapDerivedCategorySingleFunctor 0).hom.app M ∧
    (schemeOpenRestriction X' U').mapDerivedCategory.map (DerivedCategory.Qh.map qk) ≫
        (openPinnedSingleTargetRestrictionIso k U U' j hj).hom.app M =
      (schemeOpenRestriction X' U').mapDerivedCategoryFactorsh.hom.app
          ((Scheme.Modules.tensorPullback k).mapHomotopyCategory (.up ℤ) |>.obj P) ≫
        DerivedCategory.Qh.map
          ((openPinnedHomotopyTensorRestrictionIso k U U' j hj).hom.app P) ≫
        DerivedCategory.Qh.map
          ((Scheme.Modules.tensorPullback j).mapHomotopyCategory (.up ℤ) |>.map qR) ≫
        DerivedCategory.Qh.map qj := by
  dsimp only [Scheme.Modules, Scheme.ringCatSheaf] at *
  have := schemeOpenRestriction_additive X U
  have := schemeOpenRestriction_additive X' U'
  constructor
  · exact exact_single_hom (schemeOpenRestriction X U) M
  · simp only [openPinnedSingleTargetRestrictionIso, Iso.trans_hom, Iso.symm_hom,
      NatTrans.comp_app, Functor.associator_hom_app, Functor.associator_inv_app,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.id_comp, Category.comp_id,
      openPinnedHomotopyTensorRestrictionIso]
    exact derived_single_square
      (C := SheafOfModules.{u} (moduleRings X.toRingedSpace))
      (B := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
      (D := SheafOfModules.{u} (moduleRings X'.toRingedSpace))
      (E := SheafOfModules.{u} (moduleRings U'.toScheme.toRingedSpace))
      (Scheme.Modules.tensorPullback k)
      (schemeOpenRestriction X' U') (schemeOpenRestriction X U)
      (Scheme.Modules.tensorPullback j) (openPinnedTensorRestrictionIso k U U' j hj) M

/-- Public export of the private `open_pinned_single_tensor_restriction_factors_private`
(used by `import all` importers; linter.privateModule). -/
alias open_pinned_single_tensor_restriction_factors :=
  open_pinned_single_tensor_restriction_factors_private

end AlgebraicGeometry
