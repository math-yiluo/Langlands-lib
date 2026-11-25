/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
import WeilConjectures.Algebra.Homology.BifunctorSingleComparison
import WeilConjectures.Algebra.Homology.BifunctorSingleNaturality
import WeilConjectures.CategoryTheory.DerivedCategory.CochainAdjunctionCompatibility
import WeilConjectures.CategoryTheory.DerivedCategory.ExactRestrictionComposition

/-! # Realizing a scalar tower on native K-flat internal modules

This is the internal-module counterpart of the scalar realization in
`lem-pe-kflat-scalar-tower-realization`. It concerns individual scalar extensions,
their transitions and units; it involves neither products nor inverse limits.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v

open CategoryTheory MonoidalCategory MonObj Limits
open scoped CategoryTheory.Obj

namespace CategoryTheory.Mod.KFlatScalarTower

section Computation
variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C]
  [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
  [IsGrothendieckAbelian.{v} C] [Abelian.HasFunctorialFlatResolution C]
  {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
  (φ : R ⟶ S) [IsMonHom φ]
private def extendTensorIso (M : Mod C R) :
    (Mod.comap φ).obj ((Mod.extendScalars φ).obj M) ≅
      (Mod.comap φ).obj (Mod.regular S) ⊗ M := by
  let e := Mod.extendForgetTensorObjIso φ M
  have hπ : Mod.extendπ φ M ≫ e.hom =
      Mod.tensorObjπ ((Mod.comap φ).obj (Mod.regular S)) M := by
    simp [e, Mod.extendForgetTensorObjIso]
  refine Mod.isoMk e ?_
  rw [← cancel_epi (R ◁ Mod.extendπ φ M)]
  change R ◁ Mod.extendπ φ M ≫
    γ[R,((Mod.comap φ).obj (Mod.extendScalarsObj φ M)).X] ≫ e.hom =
      R ◁ Mod.extendπ φ M ≫ R ◁ e.hom ≫
        γ[R,((Mod.comap φ).obj (Mod.regular S) ⊗ M).X]
  rw [Mod.comap_obj_smul, Category.assoc, whisker_exchange_assoc,
    Mod.whiskerLeft_extendπ_smul_assoc, associator_inv_naturality_left_assoc,
    hπ, ← whiskerLeft_comp_assoc, hπ, Mod.whiskerLeft_tensorπ_smul,
    Mod.comap_obj_smul, comp_whiskerRight]
  simp only [Category.assoc]
  rfl

private def extendTensorNatIso :
    Mod.extendScalars φ ⋙ Mod.comap φ ≅
      tensorLeft ((Mod.comap φ).obj (Mod.regular S)) :=
  NatIso.ofComponents (extendTensorIso φ) (by
    intro M N f
    apply Mod.hom_ext
    simpa [extendTensorIso, Mod.extendForgetTensorIso] using
      (Mod.extendForgetTensorIso φ).hom.naturality f)

private theorem derivedUnit_homotopy
    (Y : HomotopyCategory (Mod C R) (.up ℤ)) :
    (Mod.derivedExtendMapDerivedCategoryAdjunction φ).unit.app
        (DerivedCategory.Qh.obj Y) ≫
      (Mod.comap φ).mapDerivedCategory.map
        ((Mod.extendScalars φ).leftDerivedFunctorCounit.app Y) ≫
      (Mod.comap φ).mapDerivedCategoryFactorsh.hom.app
        (((Mod.extendScalars φ).mapHomotopyCategory (.up ℤ)).obj Y) =
    DerivedCategory.Qh.map
      (((Mod.extendRestrictAdjunction φ).mapHomotopyCategory (.up ℤ)).unit.app Y) := by
  let F : Mod C R ⥤ Mod C S := Mod.extendScalars φ
  let G : Mod C S ⥤ Mod C R := Mod.comap φ
  let adj := Mod.extendRestrictAdjunction φ
  have h₁ := (adj.mapHomotopyCategory (.up ℤ)).derivedη_fac_app
    (HomotopyCategory.quasiIso (Mod C R) (.up ℤ)) F.leftDerivedFunctorCounit
    G.rightDerivedFunctorUnit Y
  have h₃ := NatTrans.congr_app G.rightDerivedFunctorIsoMapDerivedCategory_hom_fac
    ((F.mapHomotopyCategory (.up ℤ)).obj Y)
  have h₄ := G.rightDerivedFunctorIsoMapDerivedCategory.hom.naturality
    (F.leftDerivedFunctorCounit.app Y)
  dsimp at h₁ h₃ h₄
  simp only [Mod.derivedExtendMapDerivedCategoryAdjunction,
    Mod.derivedExtendRestrictAdjunction, Mod.rightDerivedComapIsoMapDerivedCategory,
    Adjunction.ofNatIsoRight_unit, NatTrans.comp_app, Functor.whiskerLeft_app,
    Category.assoc]
  rw [← reassoc_of% h₄]
  erw [reassoc_of% h₁]
  rw [reassoc_of% h₃]
  erw [Iso.inv_hom_id_app, Category.comp_id]

private def computationCounit :
    DerivedCategory.Q ⋙ (Mod.extendScalars φ).leftDerivedFunctor ⟶
      (Mod.extendScalars φ).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q := by
  let E := Mod.extendScalars φ
  let q := HomotopyCategory.quotient (Mod C R) (.up ℤ)
  let j : q ⋙ (E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) ≅
      E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (E.mapHomotopyCategoryFactors (.up ℤ)) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso (Mod C S))
  exact Functor.whiskerRight (DerivedCategory.quotientCompQhIso (Mod C R)).inv
      E.leftDerivedFunctor ≫ Functor.whiskerLeft q E.leftDerivedFunctorCounit ≫ j.hom

private theorem transpose_homotopy
    (Y : HomotopyCategory (Mod C R) (.up ℤ))
    (Z : HomotopyCategory (Mod C S) (.up ℤ))
    (f : ((Mod.extendScalars φ).mapHomotopyCategory (.up ℤ)).obj Y ⟶ Z) :
    (Mod.derivedExtendMapDerivedCategoryAdjunction φ).homEquiv _ _
      ((Mod.extendScalars φ).leftDerivedFunctorCounit.app Y ≫
        DerivedCategory.Qh.map f) =
      DerivedCategory.Qh.map
        (((Mod.extendRestrictAdjunction φ).mapHomotopyCategory (.up ℤ)).homEquiv Y Z f) ≫
        (Mod.comap φ).mapDerivedCategoryFactorsh.inv.app Z := by
  apply (cancel_mono ((Mod.comap φ).mapDerivedCategoryFactorsh.hom.app Z)).mp
  rw [Category.assoc, Iso.inv_hom_id_app]
  erw [Category.comp_id]
  rw [Adjunction.homEquiv_unit, Functor.map_comp]
  simp only [Category.assoc]
  have hn := (Mod.comap φ).mapDerivedCategoryFactorsh.hom.naturality f
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  erw [hn]
  rw [reassoc_of% (derivedUnit_homotopy φ Y), ← Functor.map_comp]
  rw [Adjunction.homEquiv_unit]

private theorem transpose_cochain
    (P : CochainComplex (Mod C R) ℤ) (Z : CochainComplex (Mod C S) ℤ)
    (f : ((Mod.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj P ⟶ Z) :
    (Mod.derivedExtendMapDerivedCategoryAdjunction φ).homEquiv _ _
      ((computationCounit φ).app P ≫ DerivedCategory.Q.map f) =
      DerivedCategory.Q.map
        (((Mod.extendRestrictAdjunction φ).mapHomologicalComplex (.up ℤ)).homEquiv P Z f) ≫
        (Mod.comap φ).mapDerivedCategoryFactors.inv.app Z := by
  exact adjunction_cochain_transpose (Mod.extendScalars φ) (Mod.comap φ)
    (Mod.extendRestrictAdjunction φ) _ (computationCounit φ) _ (fun P ↦ by
      simp [computationCounit, Functor.mapHomotopyCategoryFactors_hom_app,
        ← Functor.map_comp_assoc])
    (Mod.derivedExtendMapDerivedCategoryAdjunction φ) (transpose_homotopy φ) P Z f

variable {T : C} [MonObj T] [IsCommMonObj T]
  (ψ : S ⟶ T) [IsMonHom ψ] (χ : R ⟶ T) [IsMonHom χ]
  (h : φ ≫ ψ = χ)

private def ordinaryRestrictionComp :
    (Mod.comap ψ : Mod C T ⥤ Mod C S) ⋙ Mod.comap φ ≅ Mod.comap χ :=
  (Mod.comapComp φ ψ).symm ≪≫ Mod.comapCongr h

private def ordinaryScalarChange (M : Mod C R) :
    (Mod.extendScalars φ).obj M ⟶ (Mod.comap ψ).obj ((Mod.extendScalars χ).obj M) :=
  Mod.extendHom φ ((Mod.extendRestrictAdjunction χ).unit.app M ≫
    (ordinaryRestrictionComp φ ψ χ h).inv.app ((Mod.extendScalars χ).obj M))

omit [MonoidalPreadditive C] [Abelian.HasFunctorialFlatResolution C]
  [IsCommMonObj S] in
private theorem ordinaryUnit (M : Mod C R) :
    (Mod.extendRestrictAdjunction φ).unit.app M = Mod.extendUnit φ M := by
  rw [← Adjunction.homEquiv_id]
  simp only [Mod.extendRestrictAdjunction, Adjunction.mkOfHomEquiv_homEquiv]
  change Mod.extendUnit φ M ≫ (Mod.comap φ).map (𝟙 _) = _
  rw [(Mod.comap φ).map_id, Category.comp_id]

omit [IsCommMonObj S] [MonoidalPreadditive C]
  [Abelian.HasFunctorialFlatResolution C] [IsCommMonObj T] in
private theorem ordinaryScalarChange_pi (M : Mod C R) :
    Mod.extendπ φ M ≫ (ordinaryScalarChange φ ψ χ h M).hom =
      ψ ▷ M.X ≫ Mod.extendπ χ M  := by
  have he : ((ordinaryRestrictionComp φ ψ χ h).inv.app
      ((Mod.extendScalars χ).obj M)).hom = 𝟙 _ := by
    simp only [ordinaryRestrictionComp, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
      Mod.comp_hom', Mod.comapCongr, Mod.comapComp_hom_app_hom]
    exact Category.id_comp _
  dsimp only [ordinaryScalarChange]
  rw [Mod.extendπ_extendHom]
  simp only [Mod.comp_hom', he, ordinaryUnit, Mod.extendUnit_hom]
  erw [Category.comp_id]
  change S ◁ Mod.extendUnitHom χ M ≫
    ψ ▷ (Mod.extendScalarsObj χ M).X ≫ γ[T,(Mod.extendScalarsObj χ M).X] = _
  erw [whisker_exchange_assoc, Mod.whiskerLeft_extendUnitHom_smul']

omit [MonoidalPreadditive C] [Abelian.HasFunctorialFlatResolution C] in
private theorem ordinaryScalarChange_tensor (M : Mod C R)
    (τ : (Mod.comap φ).obj (Mod.regular S) ⟶
      (Mod.comap χ).obj (Mod.regular T)) (hτ : τ.hom = ψ) :
    (Mod.comap φ).map (ordinaryScalarChange φ ψ χ h M) ≫
      (ordinaryRestrictionComp φ ψ χ h).hom.app ((Mod.extendScalars χ).obj M) ≫
      (extendTensorNatIso χ).hom.app M =
    (extendTensorNatIso φ).hom.app M ≫ τ ▷ M := by
  apply Mod.hom_ext
  rw [← cancel_epi (Mod.extendπ φ M)]
  simp only [Mod.comp_hom', Mod.comap_map_hom, ordinaryRestrictionComp,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Mod.comapComp_inv_app_hom, Mod.comapCongr_hom_app_hom]
  erw [Category.id_comp, Category.id_comp]
  change Mod.extendπ φ M ≫ (ordinaryScalarChange φ ψ χ h M).hom ≫
      (extendTensorIso χ M).hom.hom =
    Mod.extendπ φ M ≫ (extendTensorIso φ M).hom.hom ≫ (τ ▷ M).hom
  rw [← Category.assoc, ordinaryScalarChange_pi]
  have hπ (a : R ⟶ T) [IsMonHom a] : Mod.extendπ a M ≫
      (extendTensorIso a M).hom.hom = Mod.tensorObjπ ((Mod.comap a).obj (Mod.regular T)) M := by
    simp [extendTensorIso, Mod.extendForgetTensorObjIso]
  have hπ' : Mod.extendπ φ M ≫ (extendTensorIso φ M).hom.hom =
      Mod.tensorObjπ ((Mod.comap φ).obj (Mod.regular S)) M := by
    simp [extendTensorIso, Mod.extendForgetTensorObjIso]
  simp only [Category.assoc]
  erw [hπ χ, ← Category.assoc, hπ', Mod.tensorObjπ_whiskerRight, hτ]

private def ordinaryScalarChangeNat :
    Mod.extendScalars φ ⟶ Mod.extendScalars χ ⋙ Mod.comap ψ where
  app := ordinaryScalarChange φ ψ χ h
  naturality M N f := by
    apply Mod.hom_ext
    rw [← cancel_epi (Mod.extendπ φ M)]
    simp only [Mod.comp_hom']
    change Mod.extendπ φ M ≫ (Mod.extendScalarsMap φ f).hom ≫
      (ordinaryScalarChange φ ψ χ h N).hom =
      Mod.extendπ φ M ≫ (ordinaryScalarChange φ ψ χ h M).hom ≫
        (Mod.extendScalarsMap χ f).hom
    erw [← Category.assoc, Mod.extendπ_extendScalarsMap,
      Category.assoc, ordinaryScalarChange_pi,
      reassoc_of% (ordinaryScalarChange_pi φ ψ χ h M),
      Mod.extendπ_extendScalarsMap, whisker_exchange_assoc]

private def ordinaryChangeComplex (P : CochainComplex (Mod C R) ℤ) :
    ((Mod.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj P ⟶
      ((Mod.comap ψ).mapHomologicalComplex (.up ℤ)).obj
        (((Mod.extendScalars χ).mapHomologicalComplex (.up ℤ)).obj P) :=
  (NatTrans.mapHomologicalComplex (ordinaryScalarChangeNat φ ψ χ h) (.up ℤ)).app P

omit [IsCommMonObj S] [Abelian.HasFunctorialFlatResolution C] [IsCommMonObj T] in
private theorem ordinaryChangeComplex_transpose (P : CochainComplex (Mod C R) ℤ) :
    (((Mod.extendRestrictAdjunction φ).mapHomologicalComplex (.up ℤ)).homEquiv _ _
      (ordinaryChangeComplex φ ψ χ h P)) =
    ((Mod.extendRestrictAdjunction χ).mapHomologicalComplex (.up ℤ)).unit.app P ≫
      (NatIso.mapHomologicalComplex (ordinaryRestrictionComp φ ψ χ h) (.up ℤ)).inv.app
        (((Mod.extendScalars χ).mapHomologicalComplex (.up ℤ)).obj P) := by
  rw [Adjunction.homEquiv_unit]
  ext i : 1
  change (Mod.extendRestrictAdjunction φ).unit.app (P.X i) ≫
    (Mod.comap φ).map (ordinaryScalarChange φ ψ χ h (P.X i)) = _
  rw [ordinaryUnit]
  exact (Mod.extendHomEquiv φ (P.X i) _).apply_symm_apply _

private theorem composedTranspose {A B D : Type*} [Category A] [Category B] [Category D]
    {F : A ⥤ B} {G : B ⥤ A} {H : B ⥤ D} {I : D ⥤ B}
    {L : A ⥤ D} {R : D ⥤ A}
    (a : F ⊣ G) (b : H ⊣ I) (c : L ⊣ R) (e : I ⋙ G ≅ R)
    (X : A) (Y : D) (f : L.obj X ⟶ Y) :
    a.homEquiv X (I.obj Y)
      (b.unit.app (F.obj X) ≫ I.map
        ((((a.comp b).ofNatIsoRight e).leftAdjointUniq c).hom.app X ≫ f)) =
    c.homEquiv X Y f ≫ e.inv.app Y := by
  apply (cancel_mono (e.hom.app Y)).mp
  rw [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  rw [← b.homEquiv_unit]
  have hc := congrFun (congrFun (Adjunction.comp_homEquiv a b) X) Y
  rw [← Equiv.trans_apply, ← hc]
  have he := Adjunction.homEquiv_ofNatIsoRight_apply (a.comp b) e
    ((((a.comp b).ofNatIsoRight e).leftAdjointUniq c).hom.app X ≫ f)
  apply he.symm.trans
  rw [Adjunction.homEquiv_naturality_right,
    Adjunction.homEquiv_leftAdjointUniq_hom_app, Adjunction.homEquiv_unit]

private def derivedRestrictionComp :
    (Mod.comap ψ : Mod C T ⥤ Mod C S).mapDerivedCategory ⋙
      (Mod.comap φ).mapDerivedCategory ≅
      (Mod.comap χ).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso (Mod.comap ψ) (Mod.comap φ)) ≪≫
    Functor.mapDerivedCategoryNatIso (ordinaryRestrictionComp φ ψ χ h)

private def derivedAssociation :
    (Mod.extendScalars φ).leftDerivedFunctor ⋙ (Mod.extendScalars ψ).leftDerivedFunctor ≅
      (Mod.extendScalars χ).leftDerivedFunctor :=
  (((Mod.derivedExtendMapDerivedCategoryAdjunction φ).comp
    (Mod.derivedExtendMapDerivedCategoryAdjunction ψ)).ofNatIsoRight
      (derivedRestrictionComp φ ψ χ h)).leftAdjointUniq
        (Mod.derivedExtendMapDerivedCategoryAdjunction χ)

private def rawDerivedStep (K : DerivedCategory (Mod C R)) :
    (Mod.extendScalars φ).leftDerivedFunctor.obj K ⟶
      (Mod.comap ψ).mapDerivedCategory.obj
        ((Mod.extendScalars χ).leftDerivedFunctor.obj K) :=
  (Mod.derivedExtendMapDerivedCategoryAdjunction ψ).unit.app _ ≫
    (Mod.comap ψ).mapDerivedCategory.map ((derivedAssociation φ ψ χ h).hom.app K)

private theorem rawDerivedStep_transpose (K : DerivedCategory (Mod C R)) :
    (Mod.derivedExtendMapDerivedCategoryAdjunction φ).homEquiv _ _
      (rawDerivedStep φ ψ χ h K) =
    (Mod.derivedExtendMapDerivedCategoryAdjunction χ).unit.app K ≫
      (derivedRestrictionComp φ ψ χ h).inv.app _ := by
  have ht := composedTranspose
    (Mod.derivedExtendMapDerivedCategoryAdjunction φ)
    (Mod.derivedExtendMapDerivedCategoryAdjunction ψ)
    (Mod.derivedExtendMapDerivedCategoryAdjunction χ)
    (derivedRestrictionComp φ ψ χ h) K _ (𝟙 _)
  simpa only [Category.comp_id, Adjunction.homEquiv_id, rawDerivedStep,
    derivedAssociation] using ht

omit [SymmetricCategory C] [Abelian.HasFunctorialFlatResolution C]
  [IsCommMonObj R] [IsCommMonObj S] [IsCommMonObj T] in
private theorem restriction_inv_factor (Z : CochainComplex (Mod C T) ℤ) :
    DerivedCategory.Q.map
      ((NatIso.mapHomologicalComplex (ordinaryRestrictionComp φ ψ χ h) (.up ℤ)).inv.app Z) ≫
      (Mod.comap φ).mapDerivedCategoryFactors.inv.app
        (((Mod.comap ψ).mapHomologicalComplex (.up ℤ)).obj Z) ≫
      (Mod.comap φ).mapDerivedCategory.map
        ((Mod.comap ψ).mapDerivedCategoryFactors.inv.app Z) =
    (Mod.comap χ).mapDerivedCategoryFactors.inv.app Z ≫
      (derivedRestrictionComp φ ψ χ h).inv.app (DerivedCategory.Q.obj Z) := by
  have hf := Functor.exactDerivedRestrictionComposition_inv_factors
    (Mod.comap ψ) (Mod.comap φ) (Mod.comap χ)
    (ordinaryRestrictionComp φ ψ χ h) Z
  change (Mod.comap φ).mapDerivedCategoryFactors.inv.app _ ≫
    (Mod.comap φ).mapDerivedCategory.map _ ≫
    (derivedRestrictionComp φ ψ χ h).hom.app _ = _ at hf
  have hh := congrArg (fun k ↦ DerivedCategory.Q.map
    ((NatIso.mapHomologicalComplex (ordinaryRestrictionComp φ ψ χ h) (.up ℤ)).inv.app Z) ≫
      k ≫ (derivedRestrictionComp φ ψ χ h).inv.app (DerivedCategory.Q.obj Z)) hf
  simp only [Category.assoc, Iso.hom_inv_id_app] at hh
  erw [Category.comp_id, ← DerivedCategory.Q.map_comp_assoc, Iso.inv_hom_id_app,
    DerivedCategory.Q.map_id, Category.id_comp] at hh
  exact hh

private theorem computationCounit_unit_inv (P : CochainComplex (Mod C R) ℤ) :
    (Mod.derivedExtendMapDerivedCategoryAdjunction φ).unit.app (DerivedCategory.Q.obj P) ≫
      (Mod.comap φ).mapDerivedCategory.map ((computationCounit φ).app P) =
    DerivedCategory.Q.map
      (((Mod.extendRestrictAdjunction φ).mapHomologicalComplex (.up ℤ)).unit.app P) ≫
      (Mod.comap φ).mapDerivedCategoryFactors.inv.app
        (((Mod.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj P) := by
  have hh := transpose_cochain φ P
    (((Mod.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj P) (𝟙 _)
  erw [DerivedCategory.Q.map_id, Category.comp_id, Adjunction.homEquiv_id,
    Adjunction.homEquiv_unit] at hh
  exact hh

private theorem rawStep_computation (P : CochainComplex (Mod C R) ℤ) :
    (computationCounit φ).app P ≫ DerivedCategory.Q.map (ordinaryChangeComplex φ ψ χ h P) ≫
      (Mod.comap ψ).mapDerivedCategoryFactors.inv.app
        (((Mod.extendScalars χ).mapHomologicalComplex (.up ℤ)).obj P) =
    rawDerivedStep φ ψ χ h (DerivedCategory.Q.obj P) ≫
      (Mod.comap ψ).mapDerivedCategory.map ((computationCounit χ).app P) := by
  apply ((Mod.derivedExtendMapDerivedCategoryAdjunction φ).homEquiv _ _).injective
  rw [← Category.assoc, Adjunction.homEquiv_naturality_right]
  erw [transpose_cochain, ordinaryChangeComplex_transpose]
  simp only [DerivedCategory.Q.map_comp, Category.assoc]
  rw [restriction_inv_factor]
  rw [Adjunction.homEquiv_naturality_right, rawDerivedStep_transpose]
  simp only [Category.assoc]
  have hn := (derivedRestrictionComp φ ψ χ h).inv.naturality ((computationCounit χ).app P)
  dsimp only [Functor.comp_map] at hn
  erw [← hn]
  erw [reassoc_of% (computationCounit_unit_inv χ P)]
  rfl

omit [SymmetricCategory C] [Abelian.HasFunctorialFlatResolution C]
  [IsCommMonObj R] [IsCommMonObj S] [IsCommMonObj T] in
private theorem restriction_hom_factor (Z : CochainComplex (Mod C T) ℤ) :
    (Mod.comap φ).mapDerivedCategory.map
        ((Mod.comap ψ).mapDerivedCategoryFactors.inv.app Z) ≫
      (derivedRestrictionComp φ ψ χ h).hom.app (DerivedCategory.Q.obj Z) ≫
      (Mod.comap χ).mapDerivedCategoryFactors.hom.app Z =
    (Mod.comap φ).mapDerivedCategoryFactors.hom.app
        (((Mod.comap ψ).mapHomologicalComplex (.up ℤ)).obj Z) ≫
      DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex (ordinaryRestrictionComp φ ψ χ h) (.up ℤ)).hom.app Z)
      := by
  have hf := Functor.exactDerivedRestrictionComposition_hom_factors
    (Mod.comap ψ) (Mod.comap φ) (Mod.comap χ)
    (ordinaryRestrictionComp φ ψ χ h) Z
  change (derivedRestrictionComp φ ψ χ h).hom.app _ ≫ _ = _ at hf
  erw [hf]
  rw [← (Mod.comap φ).mapDerivedCategory.map_comp_assoc, Iso.inv_hom_id_app,
    (Mod.comap φ).mapDerivedCategory.map_id, Category.id_comp]

private def computationLeft (P : CochainComplex (Mod C R) ℤ) :
    (Mod.comap φ).mapDerivedCategory.obj
      ((Mod.extendScalars φ).leftDerivedFunctor.obj (DerivedCategory.Q.obj P)) ⟶
      DerivedCategory.Q.obj
        (((tensorLeft ((Mod.comap φ).obj (Mod.regular S))).mapHomologicalComplex
          (.up ℤ)).obj P) :=
  (Mod.comap φ).mapDerivedCategory.map ((computationCounit φ).app P) ≫
    (Mod.comap φ).mapDerivedCategoryFactors.hom.app _ ≫
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
        (extendTensorNatIso φ) (.up ℤ)).hom.app P)

private theorem computationLeft_step (P : CochainComplex (Mod C R) ℤ)
    (τ : (Mod.comap φ).obj (Mod.regular S) ⟶
      (Mod.comap χ).obj (Mod.regular T)) (hτ : τ.hom = ψ) :
    (Mod.comap φ).mapDerivedCategory.map
      (rawDerivedStep φ ψ χ h (DerivedCategory.Q.obj P)) ≫
        (derivedRestrictionComp φ ψ χ h).hom.app _ ≫ computationLeft χ P =
    computationLeft φ P ≫ DerivedCategory.Q.map
      ((NatTrans.mapHomologicalComplex ((tensoringLeft (Mod C R)).map τ) (.up ℤ)).app P)
      := by
  dsimp only [computationLeft]
  simp only [Category.assoc]
  have hn := (derivedRestrictionComp φ ψ χ h).hom.naturality ((computationCounit χ).app P)
  dsimp only [Functor.comp_map] at hn
  erw [← reassoc_of% hn]
  rw [← (Mod.comap φ).mapDerivedCategory.map_comp_assoc, ← rawStep_computation]
  simp only [(Mod.comap φ).mapDerivedCategory.map_comp, Category.assoc]
  erw [reassoc_of% (restriction_hom_factor φ ψ χ h
    (((Mod.extendScalars χ).mapHomologicalComplex (.up ℤ)).obj P))]
  have hk := (Mod.comap φ).mapDerivedCategoryFactors.hom.naturality
    (ordinaryChangeComplex φ ψ χ h P)
  dsimp only [Functor.comp_map] at hk
  erw [reassoc_of% hk]
  erw [← DerivedCategory.Q.map_comp]
  have ht : ((Mod.comap φ).mapHomologicalComplex (.up ℤ)).map
      (ordinaryChangeComplex φ ψ χ h P) ≫
      (NatIso.mapHomologicalComplex (ordinaryRestrictionComp φ ψ χ h) (.up ℤ)).hom.app
        (((Mod.extendScalars χ).mapHomologicalComplex (.up ℤ)).obj P) ≫
      (NatIso.mapHomologicalComplex (extendTensorNatIso χ) (.up ℤ)).hom.app P =
    (NatIso.mapHomologicalComplex (extendTensorNatIso φ) (.up ℤ)).hom.app P ≫
      (NatTrans.mapHomologicalComplex ((tensoringLeft (Mod C R)).map τ) (.up ℤ)).app P := by
    ext i : 1
    exact ordinaryScalarChange_tensor φ ψ χ h (P.X i) τ hτ
  have hq := congrArg DerivedCategory.Q.map ht
  simp only [DerivedCategory.Q.map_comp] at hq
  simpa only [DerivedCategory.Q.map_comp, Category.assoc] using
    congrArg (fun k ↦ (Mod.comap φ).mapDerivedCategory.map
      ((computationCounit φ).app P) ≫
        (Mod.comap φ).mapDerivedCategoryFactors.hom.app _ ≫ k) hq

omit [MonoidalPreadditive C] [Abelian.HasFunctorialFlatResolution C] in
private theorem leftUnitor_inv_hom (M : Mod C R) :
    (λ_ M).inv.hom = (λ_ M.X).inv ≫ η[R] ▷ M.X ≫
      Mod.tensorObjπ (Mod.regular R) M := by
  change Bimod.LeftUnitorBimod.inv ((Mod.toBimod R).obj M) ≫
    (Bimod.whiskerRight (Mod.toBimodRegularIso (R := R)).inv
      ((Mod.toBimod R).obj M)).hom = _
  change ((λ_ M.X).inv ≫ η[R] ▷ M.X ≫ coequalizer.π _ _) ≫
    colimMap _ = _
  simp only [Category.assoc, ι_colimMap, parallelPairHom_app_one,
    Mod.toBimodRegularIso_inv_hom]
  erw [MonoidalCategory.id_whiskerRight, Category.id_comp]
  rfl

omit [MonoidalPreadditive C] [Abelian.HasFunctorialFlatResolution C] in
private theorem ordinaryUnit_tensorLeft (M : Mod C R)
    (ι : Mod.regular R ⟶ (Mod.comap φ).obj (Mod.regular S)) (hι : ι.hom = φ) :
    (Mod.extendRestrictAdjunction φ).unit.app M ≫ (extendTensorIso φ M).hom =
      (λ_ M).inv ≫ ι ▷ M := by
  have hu : (Mod.extendRestrictAdjunction φ).unit.app M = Mod.extendUnit φ M := by
    rw [← Adjunction.homEquiv_id]
    simp only [Mod.extendRestrictAdjunction, Adjunction.mkOfHomEquiv_homEquiv]
    change Mod.extendUnit φ M ≫ (Mod.comap φ).map (𝟙 _) = _
    rw [(Mod.comap φ).map_id, Category.comp_id]
  rw [hu]
  apply Mod.hom_ext
  simp only [Mod.comp_hom', Mod.extendUnit_hom, leftUnitor_inv_hom,
    Category.assoc, Mod.tensorObjπ_whiskerRight, hι]
  change Mod.extendUnitHom φ M ≫ (extendTensorIso φ M).hom.hom = _
  dsimp only [Mod.extendUnitHom]
  simp only [Category.assoc]
  have hπ : Mod.extendπ φ M ≫ (extendTensorIso φ M).hom.hom =
      Mod.tensorObjπ ((Mod.comap φ).obj (Mod.regular S)) M := by
    simp [extendTensorIso, Mod.extendForgetTensorObjIso]
  erw [hπ, ← comp_whiskerRight_assoc]
  have hη : η[R] ≫ φ = η[S] := IsMonHom.one_hom φ
  rw [hη]

private def extendTensorRightNatIso :
    Mod.extendScalars φ ⋙ Mod.comap φ ≅
      tensorRight ((Mod.comap φ).obj (Mod.regular S)) :=
  extendTensorNatIso φ ≪≫
    BraidedCategory.tensorLeftIsoTensorRight ((Mod.comap φ).obj (Mod.regular S))

omit [MonoidalPreadditive C] [Abelian.HasFunctorialFlatResolution C] in
private theorem ordinaryUnit_tensorRight (M : Mod C R)
    (ι : Mod.regular R ⟶ (Mod.comap φ).obj (Mod.regular S)) (hι : ι.hom = φ) :
    (Mod.extendRestrictAdjunction φ).unit.app M ≫ (extendTensorRightNatIso φ).hom.app M =
      (ρ_ M).inv ≫ M ◁ ι := by
  change (Mod.extendRestrictAdjunction φ).unit.app M ≫
    (extendTensorIso φ M).hom ≫ (β_ ((Mod.comap φ).obj (Mod.regular S)) M).hom = _
  rw [← Category.assoc, ordinaryUnit_tensorLeft φ M ι hι, Category.assoc,
    BraidedCategory.braiding_naturality_left, ← Category.assoc]
  exact congrArg (fun k ↦ k ≫ M ◁ ι) (leftUnitor_inv_braiding M)

private def computationRight (P : CochainComplex (Mod C R) ℤ) :
    (Mod.comap φ).mapDerivedCategory.obj
      ((Mod.extendScalars φ).leftDerivedFunctor.obj (DerivedCategory.Q.obj P)) ⟶
      DerivedCategory.Q.obj
        (((tensorRight ((Mod.comap φ).obj (Mod.regular S))).mapHomologicalComplex
          (.up ℤ)).obj P) :=
  (Mod.comap φ).mapDerivedCategory.map ((computationCounit φ).app P) ≫
    (Mod.comap φ).mapDerivedCategoryFactors.hom.app _ ≫
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
        (extendTensorRightNatIso φ) (.up ℤ)).hom.app P)

private theorem computationRight_isIso (P : CochainComplex (Mod C R) ℤ)
    (hP : (HomologicalComplex.quasiIso (Mod C R) (.up ℤ)).kFlat P) :
    IsIso (computationRight φ P) := by
  have : IsIso ((Mod.extendScalars φ).leftDerivedFunctorCounit.app
      ((HomotopyCategory.quotient (Mod C R) (.up ℤ)).obj P)) :=
    (Mod.extendScalars φ).isIso_leftDerivedFunctorCounit_app_of_kFlat P hP
  have : IsIso ((computationCounit φ).app P) := by
    dsimp only [computationCounit, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app]
    infer_instance
  dsimp only [computationRight]
  infer_instance

private theorem computationCounit_unit (P : CochainComplex (Mod C R) ℤ) :
    (Mod.derivedExtendMapDerivedCategoryAdjunction φ).unit.app (DerivedCategory.Q.obj P) ≫
      (Mod.comap φ).mapDerivedCategory.map ((computationCounit φ).app P) ≫
      (Mod.comap φ).mapDerivedCategoryFactors.hom.app
        (((Mod.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj P) =
      DerivedCategory.Q.map
        (((Mod.extendRestrictAdjunction φ).mapHomologicalComplex (.up ℤ)).unit.app P) := by
  have h := transpose_cochain φ P
    (((Mod.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj P) (𝟙 _)
  erw [DerivedCategory.Q.map_id, Category.comp_id, Adjunction.homEquiv_id,
    Adjunction.homEquiv_unit] at h
  have hh := congrArg (fun k ↦ k ≫ (Mod.comap φ).mapDerivedCategoryFactors.hom.app
    (((Mod.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj P)) h
  simp only [Category.assoc, Iso.inv_hom_id_app] at hh
  erw [Category.comp_id] at hh
  exact hh

private theorem computationRight_unit (P : CochainComplex (Mod C R) ℤ)
    (ι : Mod.regular R ⟶ (Mod.comap φ).obj (Mod.regular S)) (hι : ι.hom = φ) :
    (Mod.derivedExtendMapDerivedCategoryAdjunction φ).unit.app (DerivedCategory.Q.obj P) ≫
      computationRight φ P =
      DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex ((rightUnitorNatIso (Mod C R)).inv ≫
          (tensoringRight (Mod C R)).map ι) (.up ℤ)).app P) := by
  dsimp only [computationRight]
  erw [reassoc_of% (computationCounit_unit φ P), ← DerivedCategory.Q.map_comp]
  congr 1
  ext i : 1
  exact ordinaryUnit_tensorRight φ (P.X i) ι hι

private theorem computationRight_step (P : CochainComplex (Mod C R) ℤ)
    (τ : (Mod.comap φ).obj (Mod.regular S) ⟶
      (Mod.comap χ).obj (Mod.regular T)) (hτ : τ.hom = ψ) :
    (Mod.comap φ).mapDerivedCategory.map
      (rawDerivedStep φ ψ χ h (DerivedCategory.Q.obj P)) ≫
        (derivedRestrictionComp φ ψ χ h).hom.app _ ≫ computationRight χ P =
    computationRight φ P ≫ DerivedCategory.Q.map
      ((NatTrans.mapHomologicalComplex ((tensoringRight (Mod C R)).map τ) (.up ℤ)).app P)
      := by
  have hc (a : R ⟶ T) [IsMonHom a] : computationRight a P =
      computationLeft a P ≫ DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex
          (BraidedCategory.tensorLeftIsoTensorRight ((Mod.comap a).obj (Mod.regular T)))
            (.up ℤ)).hom.app P) := by
    dsimp only [computationRight, computationLeft, extendTensorRightNatIso]
    simp only [Category.assoc]
    rw [← DerivedCategory.Q.map_comp]
    congr 2
  have hc' : computationRight φ P = computationLeft φ P ≫ DerivedCategory.Q.map
      ((NatIso.mapHomologicalComplex
        (BraidedCategory.tensorLeftIsoTensorRight ((Mod.comap φ).obj (Mod.regular S)))
          (.up ℤ)).hom.app P) := by
    dsimp only [computationRight, computationLeft, extendTensorRightNatIso]
    simp only [Category.assoc]
    rw [← DerivedCategory.Q.map_comp]
    congr 2
  rw [hc χ, hc']
  simp only [Category.assoc]
  erw [reassoc_of% (computationLeft_step φ ψ χ h P τ hτ)]
  have hn :
      (NatTrans.mapHomologicalComplex ((tensoringLeft (Mod C R)).map τ) (.up ℤ)).app P ≫
        (NatIso.mapHomologicalComplex
          (BraidedCategory.tensorLeftIsoTensorRight ((Mod.comap χ).obj (Mod.regular T)))
            (.up ℤ)).hom.app P =
      (NatIso.mapHomologicalComplex
        (BraidedCategory.tensorLeftIsoTensorRight ((Mod.comap φ).obj (Mod.regular S)))
          (.up ℤ)).hom.app P ≫
        (NatTrans.mapHomologicalComplex ((tensoringRight (Mod C R)).map τ) (.up ℤ)).app P
        := by
    ext i : 1
    exact BraidedCategory.braiding_naturality_left τ (P.X i)
  have hq := congrArg DerivedCategory.Q.map hn
  simp only [DerivedCategory.Q.map_comp] at hq
  exact congrArg (fun k ↦ computationLeft φ P ≫ k) hq

end Computation

attribute [local irreducible] extendTensorIso extendTensorNatIso extendTensorRightNatIso

section TensorTransport
variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C]
  [MonoidalPreadditive C]

private theorem transportTensorUnit {B B' : C} (e : B ≅ B')
    (ι : 𝟙_ C ⟶ B) (P : CochainComplex C ℤ) :
    (NatTrans.mapHomologicalComplex
      ((rightUnitorNatIso C).inv ≫ (tensoringRight C).map (ι ≫ e.hom)) (.up ℤ)).app P ≫
      (NatIso.mapHomologicalComplex ((tensoringRight C).mapIso e) (.up ℤ)).inv.app P =
    (NatTrans.mapHomologicalComplex
      ((rightUnitorNatIso C).inv ≫ (tensoringRight C).map ι) (.up ℤ)).app P := by
  ext i : 1
  change ((ρ_ (P.X i)).inv ≫ (P.X i) ◁ (ι ≫ e.hom)) ≫ (P.X i) ◁ e.inv =
    (ρ_ (P.X i)).inv ≫ (P.X i) ◁ ι
  simp only [Category.assoc, ← whiskerLeft_comp, Iso.hom_inv_id, Category.comp_id]

private theorem transportTensorStep {B B' D D' : C}
    (e : B ≅ B') (f : D ≅ D') (τ : B ⟶ D) (τ' : B' ⟶ D')
    (h : τ ≫ f.hom = e.hom ≫ τ') (P : CochainComplex C ℤ) :
    (NatTrans.mapHomologicalComplex ((tensoringRight C).map τ') (.up ℤ)).app P ≫
      (NatIso.mapHomologicalComplex ((tensoringRight C).mapIso f) (.up ℤ)).inv.app P =
    (NatIso.mapHomologicalComplex ((tensoringRight C).mapIso e) (.up ℤ)).inv.app P ≫
      (NatTrans.mapHomologicalComplex ((tensoringRight C).map τ) (.up ℤ)).app P := by
  have hh : τ' ≫ f.inv = e.inv ≫ τ := by
    apply (cancel_epi e.hom).mp
    simp only [Iso.hom_inv_id_assoc]
    rw [← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  ext i : 1
  change (P.X i) ◁ τ' ≫ (P.X i) ◁ f.inv =
    (P.X i) ◁ e.inv ≫ (P.X i) ◁ τ
  simp only [← whiskerLeft_comp, hh]

end TensorTransport

section StepNaturality
private theorem towerStep_naturality
    {A B D : Type*} [Category A] [Category B] [Category D]
    {F : A ⥤ B} {G : B ⥤ A} {H : B ⥤ D} {I : D ⥤ B}
    {L : A ⥤ D} {R : D ⥤ A}
    (b : H ⊣ I) (e : F ⋙ H ≅ L) (c : I ⋙ G ≅ R)
    {X Y : A} (f : X ⟶ Y) :
    G.map (F.map f) ≫
      G.map (b.unit.app (F.obj Y) ≫ I.map (e.hom.app Y)) ≫ c.hom.app (L.obj Y) =
    G.map (b.unit.app (F.obj X) ≫ I.map (e.hom.app X)) ≫ c.hom.app (L.obj X) ≫
      R.map (L.map f) := by
  let η₀ : F ⟶ L ⋙ I :=
    CategoryTheory.Functor.whiskerLeft F b.unit ≫ CategoryTheory.Functor.whiskerRight e.hom I
  let θ : F ⋙ G ⟶ L ⋙ R :=
    CategoryTheory.Functor.whiskerRight η₀ G ≫ CategoryTheory.Functor.whiskerLeft L c.hom
  simpa only [θ, η₀, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Category.assoc, Functor.comp_map] using θ.naturality f

end StepNaturality

section RepresentativeTransport
end RepresentativeTransport

variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C]
  [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
  [IsGrothendieckAbelian.{v} C] [Abelian.HasFunctorialFlatResolution C]
  (R : C) [MonObj R] [IsCommMonObj R]
  (S : ℕ → C) [∀ n, MonObj (S n)] [∀ n, IsCommMonObj (S n)]
  (q : ∀ n, R ⟶ S n) [∀ n, IsMonHom (q n)]
  (r : ∀ n, S (n + 1) ⟶ S n) [∀ n, IsMonHom (r n)]
  (h : ∀ n, q (n + 1) ≫ r n = q n)

/-- Derived scalar extension at a single level. -/
abbrev reduction (n : ℕ) : DerivedCategory (Mod C R) ⥤ DerivedCategory (Mod C (S n)) :=
  (Mod.extendScalars (q n)).leftDerivedFunctor

/-- Exact restriction at a single level. -/
abbrev restriction (n : ℕ) : DerivedCategory (Mod C (S n)) ⥤ DerivedCategory (Mod C R) :=
  (Mod.comap (q n)).mapDerivedCategory

/-- Restriction composition, with its specified quotient-factor equality. -/
def restrictionComp (n : ℕ) :
    (Mod.comap (r n)).mapDerivedCategory ⋙ restriction R S q (n + 1) ≅
      restriction R S q n :=
  (Functor.mapDerivedCategoryCompIso (Mod.comap (r n)) (Mod.comap (q (n + 1)))) ≪≫
    Functor.mapDerivedCategoryNatIso
      ((Mod.comapComp (q (n + 1)) (r n)).symm ≪≫ Mod.comapCongr (h n))

/-- Association determined by the extension-restriction adjunctions. -/
def association (n : ℕ) :
    reduction R S q (n + 1) ⋙ (Mod.extendScalars (r n)).leftDerivedFunctor ≅
      reduction R S q n :=
  (((Mod.derivedExtendMapDerivedCategoryAdjunction (q (n + 1))).comp
    (Mod.derivedExtendMapDerivedCategoryAdjunction (r n))).ofNatIsoRight
      (restrictionComp R S q r h n)).leftAdjointUniq
    (Mod.derivedExtendMapDerivedCategoryAdjunction (q n))

/-- The canonical transition after restriction to the common ring. -/
def step (K : DerivedCategory (Mod C R)) (n : ℕ) :
    (restriction R S q (n + 1)).obj ((reduction R S q (n + 1)).obj K) ⟶
      (restriction R S q n).obj ((reduction R S q n).obj K) :=
  (restriction R S q (n + 1)).map
    ((Mod.derivedExtendMapDerivedCategoryAdjunction (r n)).unit.app
      ((reduction R S q (n + 1)).obj K) ≫
        (Mod.comap (r n)).mapDerivedCategory.map ((association R S q r h n).hom.app K)) ≫
    (restrictionComp R S q r h n).hom.app ((reduction R S q n).obj K)

variable (B : ℕ → Mod C R) (ι : ∀ n, 𝟙_ (Mod C R) ⟶ B n)
  (τ : ∀ n, B (n + 1) ⟶ B n)

/-- Termwise tensor reduction. -/
abbrev tensorLevel (n : ℕ) := (tensorRight (B n)).mapHomologicalComplex (.up ℤ)

/-- Termwise tensor transition. -/
def tensorStep (P : CochainComplex (Mod C R) ℤ) (n : ℕ) :
    (tensorLevel R B (n + 1)).obj P ⟶ (tensorLevel R B n).obj P :=
  (NatTrans.mapHomologicalComplex ((tensoringRight (Mod C R)).map (τ n)) (.up ℤ)).app P

/-- The specified tensor-unit morphism. -/
def tensorUnit (P : CochainComplex (Mod C R) ℤ) (n : ℕ) :
    P ⟶ (tensorLevel R B n).obj P :=
  (NatTrans.mapHomologicalComplex
    ((rightUnitorNatIso (Mod C R)).inv ≫ (tensoringRight (Mod C R)).map (ι n))
      (.up ℤ)).app P

/-- The scalar computation is natural already on complexes, before choosing a
K-flat representative. Its components are invertible on K-flat complexes, and
its unit and transition equations use the specified adjunctions.

Source: the natural balanced comparison and computation-counit argument in
`lem-pe-internal-kflat-scalar-tower-realization`.
(auxiliary; not a blueprint node).

Proof: use the natural derived computation counit, the exact restriction
comparison and the balanced tensor comparison. Transport the coefficient by eB.
The component computations in the proof of realization give both equations;
naturality is the composition of these three natural comparisons. -/
theorem natural_computation
    (eB : ∀ n, B n ≅ (Mod.comap (q n)).obj (Mod.regular (S n)))
    (hι : ∀ n, (ι n).hom ≫ (eB n).hom.hom = q n)
    (hτ : ∀ n, (τ n).hom ≫ (eB n).hom.hom = (eB (n + 1)).hom.hom ≫ r n) :
    ∃ c : ∀ n, DerivedCategory.Q ⋙ reduction R S q n ⋙ restriction R S q n ⟶
        tensorLevel R B n ⋙ DerivedCategory.Q,
      (∀ n P, (HomologicalComplex.quasiIso (Mod C R) (.up ℤ)).kFlat P →
        IsIso ((c n).app P)) ∧
      (∀ n P, step R S q r h (DerivedCategory.Q.obj P) n ≫ (c n).app P =
        (c (n + 1)).app P ≫ DerivedCategory.Q.map (tensorStep R B τ P n)) ∧
      (∀ n P, (Mod.derivedExtendMapDerivedCategoryAdjunction (q n)).unit.app
          (DerivedCategory.Q.obj P) ≫ (c n).app P =
        DerivedCategory.Q.map (tensorUnit R B ι P n)) := by
  let transport (n : ℕ) :=
    (NatIso.mapHomologicalComplex ((tensoringRight (Mod C R)).mapIso (eB n))
      (.up ℤ)).inv
  let c (n : ℕ) : DerivedCategory.Q ⋙ reduction R S q n ⋙ restriction R S q n ⟶
      tensorLevel R B n ⋙ DerivedCategory.Q :=
    { app := fun P ↦ computationRight (q n) P ≫ DerivedCategory.Q.map ((transport n).app P)
      naturality := by
        intro P P' f
        dsimp only [Functor.comp_map, reduction, restriction]
        have hn := (computationCounit (q n)).naturality f
        have hr := (Mod.comap (q n)).mapDerivedCategoryFactors.hom.naturality
          (((Mod.extendScalars (q n)).mapHomologicalComplex (.up ℤ)).map f)
        have ht := (NatIso.mapHomologicalComplex
          (extendTensorRightNatIso (q n)) (.up ℤ)).hom.naturality f
        have hb := (transport n).naturality f
        dsimp only [Functor.comp_map] at hn hr ht hb
        dsimp only [computationRight]
        simp only [Category.assoc, ← Functor.map_comp_assoc, hn]
        simp only [Functor.map_comp, Category.assoc]
        rw [reassoc_of% hr]
        rw [← DerivedCategory.Q.map_comp_assoc]
        erw [ht]
        simp only [DerivedCategory.Q.map_comp, Category.assoc]
        rw [← DerivedCategory.Q.map_comp, hb, DerivedCategory.Q.map_comp] }
  refine ⟨c, ?_, ?_, ?_⟩
  · intro n P hP
    have := computationRight_isIso (q n) P hP
    dsimp only [c, transport]
    infer_instance
  · intro n P
    let canonicalτ := (eB (n + 1)).inv ≫ τ n ≫ (eB n).hom
    have canonicalτ_hom : canonicalτ.hom = r n := by
      dsimp only [canonicalτ]
      simp only [Mod.comp_hom']
      rw [hτ n, ← Category.assoc]
      have hi := congrArg Mod.Hom.hom (eB (n + 1)).inv_hom_id
      simp only [Mod.comp_hom'] at hi
      rw [hi]
      exact Category.id_comp _
    have hs := computationRight_step (q (n + 1)) (r n) (q n) (h n) P
      canonicalτ canonicalτ_hom
    have hs' : step R S q r h (DerivedCategory.Q.obj P) n ≫ computationRight (q n) P =
        computationRight (q (n + 1)) P ≫ DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex ((tensoringRight (Mod C R)).map
            canonicalτ) (.up ℤ)).app P) := by
      simpa only [step, rawDerivedStep, reduction, restriction, derivedAssociation,
        derivedRestrictionComp, restrictionComp, association, ordinaryRestrictionComp,
        Category.assoc] using hs
    dsimp only [c]
    rw [← Category.assoc, hs']
    simp only [Category.assoc]
    rw [← DerivedCategory.Q.map_comp]
    have ht := transportTensorStep (eB (n + 1)) (eB n) (τ n) canonicalτ
      (by simp [canonicalτ]) P
    erw [ht]
    rw [DerivedCategory.Q.map_comp]
    rfl
  · intro n P
    dsimp only [c]
    rw [← Category.assoc, computationRight_unit (q n) P (ι n ≫ (eB n).hom)]
    · rw [← DerivedCategory.Q.map_comp]
      exact congrArg DerivedCategory.Q.map (transportTensorUnit (eB n) (ι n) P)
    · exact hι n

section
set_option backward.defeqAttrib.useBackward true

namespace PrincipalTensorAux

variable {A : Type u} [Category.{v} A] [Abelian A] [MonoidalCategory A]
  [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [IsGrothendieckAbelian.{v} A] [Abelian.HasFunctorialFlatResolution A]

private abbrev single (B : A) := (HomologicalComplex.single A (.up ℤ) 0).obj B

private def tensorComparison (B : A) :
    DerivedCategory.Q ⋙ tensorRight ((DerivedCategory.singleFunctor A 0).obj B) ⟶
      (tensorRight B).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q where
  app P := Functor.LaxMonoidal.μ DerivedCategory.Q P (single B) ≫
    DerivedCategory.Q.map (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor A) B P).hom
  naturality P P' f := by
    dsimp only [Functor.comp_map]
    change (DerivedCategory.Q.map f ▷ DerivedCategory.Q.obj (single B)) ≫ _ = _
    rw [← Category.assoc, Functor.LaxMonoidal.μ_natural_left]
    simp only [Category.assoc]
    have ht := CochainComplex.mapBifunctorSingle₂Iso_hom_naturality (curriedTensor A) B f
    have ht' : f ▷ single B ≫
        (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor A) B P').hom =
      (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor A) B P).hom ≫
        ((tensorRight B).mapHomologicalComplex (.up ℤ)).map f := ht
    rw [← DerivedCategory.Q.map_comp, ht', DerivedCategory.Q.map_comp]

private theorem tensorComparison_isIso (B : A) (P : CochainComplex A ℤ)
    (hP : (HomologicalComplex.quasiIso A (.up ℤ)).kFlat P) :
    IsIso ((tensorComparison B).app P) := by
  have h := DerivedMonoidal.isIso_counit_app_app_of_kFlat_left DerivedCategory.Qh
    (HomotopyCategory.quasiIso A (.up ℤ))
    ((HomotopyCategory.quotient A (.up ℤ)).obj P)
    ((HomotopyCategory.quotient A (.up ℤ)).obj (single B))
    ((HomotopyCategory.kFlat_quotient_obj_iff _).2 hP)
  have : IsIso (Functor.LaxMonoidal.μ DerivedCategory.Qh
      ((HomotopyCategory.quotient A (.up ℤ)).obj P)
      ((HomotopyCategory.quotient A (.up ℤ)).obj (single B))) := h
  have : IsIso (Functor.LaxMonoidal.μ DerivedCategory.Q P (single B)) := by
    change IsIso ((_ ⊗ₘ _) ≫ (Functor.LaxMonoidal.μ DerivedCategory.Qh _ _ ≫
      DerivedCategory.Qh.map _) ≫ _)
    infer_instance
  dsimp only [tensorComparison]
  infer_instance

private theorem tensorComparison_step {B B' : A} (f : B ⟶ B')
    (P : CochainComplex A ℤ) :
    DerivedCategory.Q.obj P ◁ (DerivedCategory.singleFunctor A 0).map f ≫
        (tensorComparison B').app P =
      (tensorComparison B).app P ≫ DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex ((tensoringRight A).map f) (.up ℤ)).app P) := by
  dsimp only [tensorComparison]
  change (DerivedCategory.Q.obj P ◁ DerivedCategory.Q.map
    ((HomologicalComplex.single A (.up ℤ) 0).map f)) ≫ _ = _
  rw [← Category.assoc, Functor.LaxMonoidal.μ_natural_right]
  simp only [Category.assoc]
  rw [← DerivedCategory.Q.map_comp, ← DerivedCategory.Q.map_comp]
  exact congrArg (fun k ↦ Functor.LaxMonoidal.μ DerivedCategory.Q P (single B) ≫
    DerivedCategory.Q.map k)
    (CochainComplex.mapBifunctorSingle₂Iso_hom_naturality₂ (curriedTensor A) f P)

omit [Abelian.HasFunctorialFlatResolution A] in
private theorem single_unit (P : CochainComplex A ℤ) :
    (ρ_ P).inv ≫
        (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor A) (𝟙_ A) P).hom =
      (NatTrans.mapHomologicalComplex (rightUnitorNatIso A).inv (.up ℤ)).app P := by
  apply (cancel_mono
    (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor A) (𝟙_ A) P).inv).mp
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  ext i : 1
  change (HomologicalComplex.rightUnitor' P).inv i = _
  rw [HomologicalComplex.rightUnitor'_inv]
  rw [HomologicalComplex.comp_f, CochainComplex.mapBifunctorSingle₂Iso_inv_f]
  rfl

private theorem tensorComparison_unit (B : A) (ι : 𝟙_ A ⟶ B)
    (P : CochainComplex A ℤ) :
    ((ρ_ (DerivedCategory.Q.obj P)).inv ≫ DerivedCategory.Q.obj P ◁
        (Functor.LaxMonoidal.ε DerivedCategory.Q ≫ DerivedCategory.Q.map
          ((HomologicalComplex.single A (.up ℤ) 0).map ι))) ≫
        (tensorComparison B).app P =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
        ((rightUnitorNatIso A).inv ≫ (tensoringRight A).map ι) (.up ℤ)).app P) := by
  dsimp only [tensorComparison]
  rw [whiskerLeft_comp]
  simp only [Category.assoc]
  rw [Functor.LaxMonoidal.μ_natural_right_assoc,
    Functor.LaxMonoidal.right_unitality_inv_assoc]
  rw [← DerivedCategory.Q.map_comp, ← DerivedCategory.Q.map_comp]
  congr 1
  erw [CochainComplex.mapBifunctorSingle₂Iso_hom_naturality₂ (curriedTensor A) ι P]
  rw [← Category.assoc, single_unit]
  rfl

private theorem compare_step {D : Type*} [Category D]
    {A A' B B' C C' : D} (v : A ⟶ C) (v' : A' ⟶ C')
    (w : B ⟶ C) (w' : B' ⟶ C') [IsIso w] [IsIso w']
    (t : A' ⟶ A) (s : B' ⟶ B) (d : C' ⟶ C)
    (hv : t ≫ v = v' ≫ d) (hw : s ≫ w = w' ≫ d) :
    t ≫ (v ≫ inv w) = (v' ≫ inv w') ≫ s := by
  apply (cancel_mono w).mp
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [hw, IsIso.inv_hom_id_assoc, hv]

private theorem compare_unit {D : Type*} [Category D]
    {A B C O : D} (v : A ⟶ C) (w : B ⟶ C) [IsIso w]
    (a : O ⟶ A) (b : O ⟶ B) (d : O ⟶ C)
    (hv : a ≫ v = d) (hw : b ≫ w = d) : a ≫ (v ≫ inv w) = b := by
  apply (cancel_mono w).mp
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  exact hv.trans hw.symm

private theorem descend
    {C D : Type*} [Category C] [Category D]
    (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W]
    (F G : ℕ → D ⥤ D)
    (t : ∀ n, F (n + 1) ⟶ F n) (s : ∀ n, G (n + 1) ⟶ G n)
    (a : ∀ n, 𝟭 D ⟶ F n) (b : ∀ n, 𝟭 D ⟶ G n)
    (e : ∀ n, L ⋙ F n ≅ L ⋙ G n)
    (hs : ∀ n P, (t n).app (L.obj P) ≫ (e n).hom.app P =
      (e (n + 1)).hom.app P ≫ (s n).app (L.obj P))
    (hu : ∀ n P, (a n).app (L.obj P) ≫ (e n).hom.app P =
      (b n).app (L.obj P)) :
    ∃ en : ∀ n, F n ≅ G n,
      (∀ n K, (t n).app K ≫ (en n).hom.app K =
        (en (n + 1)).hom.app K ≫ (s n).app K) ∧
      (∀ n K, (a n).app K ≫ (en n).hom.app K = (b n).app K) := by
  let ff := Localization.fullyFaithfulWhiskeringLeft L W D
  let en (n : ℕ) : F n ≅ G n := ff.preimageIso (e n)
  have he (n : ℕ) (P : C) : (en n).hom.app (L.obj P) = (e n).hom.app P :=
    congrArg (fun f ↦ f.app P) (ff.map_preimage (e n).hom)
  refine ⟨en, ?_, ?_⟩
  · intro n K
    have hh : t n ≫ (en n).hom = (en (n + 1)).hom ≫ s n := by
      apply Localization.natTrans_ext L W
      intro P
      simpa only [NatTrans.comp_app, he] using hs n P
    exact congrArg (fun f ↦ f.app K) hh
  · intro n K
    have hh : a n ≫ (en n).hom = b n := by
      apply Localization.natTrans_ext L W
      intro P
      simpa only [NatTrans.comp_app, he] using hu n P
    exact congrArg (fun f ↦ f.app K) hh

private theorem descend_comparison
    {C D : Type*} [Category C] [Category D]
    (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W]
    (F G : ℕ → D ⥤ D) (H : ℕ → C ⥤ D)
    (v : ∀ n, L ⋙ F n ⟶ H n) (w : ∀ n, L ⋙ G n ⟶ H n)
    [∀ n, IsIso (v n)] [∀ n, IsIso (w n)]
    (t : ∀ n, F (n + 1) ⟶ F n) (s : ∀ n, G (n + 1) ⟶ G n)
    (a : ∀ n, 𝟭 D ⟶ F n) (b : ∀ n, 𝟭 D ⟶ G n)
    (d : ∀ n P, (H (n + 1)).obj P ⟶ (H n).obj P)
    (unit : ∀ n P, L.obj P ⟶ (H n).obj P)
    (hv : ∀ n P, (t n).app (L.obj P) ≫ (v n).app P =
      (v (n + 1)).app P ≫ d n P)
    (hw : ∀ n P, (s n).app (L.obj P) ≫ (w n).app P =
      (w (n + 1)).app P ≫ d n P)
    (hvunit : ∀ n P, (a n).app (L.obj P) ≫ (v n).app P = unit n P)
    (hwunit : ∀ n P, (b n).app (L.obj P) ≫ (w n).app P = unit n P) :
    ∃ en : ∀ n, F n ≅ G n,
      (∀ n K, (t n).app K ≫ (en n).hom.app K =
        (en (n + 1)).hom.app K ≫ (s n).app K) ∧
      (∀ n K, (a n).app K ≫ (en n).hom.app K = (b n).app K) := by
  let e (n : ℕ) : L ⋙ F n ≅ L ⋙ G n := asIso (v n) ≪≫ (asIso (w n)).symm
  apply descend L W F G t s a b e
  · intro n P
    simpa only [e, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, asIso_hom, asIso_inv,
      NatIso.isIso_inv_app] using compare_step ((v n).app P) ((v (n + 1)).app P)
      ((w n).app P) ((w (n + 1)).app P) ((t n).app (L.obj P))
      ((s n).app (L.obj P)) (d n P) (hv n P) (hw n P)
  · intro n P
    simpa only [e, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, asIso_hom, asIso_inv,
      NatIso.isIso_inv_app] using compare_unit ((v n).app P) ((w n).app P)
      ((a n).app (L.obj P)) ((b n).app (L.obj P)) (unit n P) (hvunit n P) (hwunit n P)

private theorem realize
    (B : ℕ → A) (ι : ∀ n, 𝟙_ A ⟶ B n) (τ : ∀ n, B (n + 1) ⟶ B n)
    (G : ℕ → DerivedCategory A ⥤ DerivedCategory A)
    (s : ∀ n, G (n + 1) ⟶ G n) (b : ∀ n, 𝟭 _ ⟶ G n)
    (c : ∀ n, DerivedCategory.Q ⋙ G n ⟶
      (tensorRight (B n)).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (hc : ∀ n P, (HomologicalComplex.quasiIso A (.up ℤ)).kFlat P →
      IsIso ((c n).app P))
    (hs : ∀ n P, (s n).app (DerivedCategory.Q.obj P) ≫ (c n).app P =
      (c (n + 1)).app P ≫ DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex ((tensoringRight A).map (τ n)) (.up ℤ)).app P))
    (hu : ∀ n P, (b n).app (DerivedCategory.Q.obj P) ≫ (c n).app P =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
        ((rightUnitorNatIso A).inv ≫ (tensoringRight A).map (ι n)) (.up ℤ)).app P)) :
    ∃ e : ∀ n, tensorRight ((DerivedCategory.singleFunctor A 0).obj (B n)) ≅ G n,
      (∀ n K, (K ◁ (DerivedCategory.singleFunctor A 0).map (τ n)) ≫
        (e n).hom.app K = (e (n + 1)).hom.app K ≫ (s n).app K) ∧
      (∀ n K, ((ρ_ K).inv ≫ K ◁
          (Functor.LaxMonoidal.ε DerivedCategory.Q ≫ DerivedCategory.Q.map
            ((HomologicalComplex.single A (.up ℤ) 0).map (ι n)))) ≫
        (e n).hom.app K = (b n).app K) := by
  let F (n : ℕ) := tensorRight ((DerivedCategory.singleFunctor A 0).obj (B n))
  let t (n : ℕ) : F (n + 1) ⟶ F n :=
    (tensoringRight _).map ((DerivedCategory.singleFunctor A 0).map (τ n))
  let a (n : ℕ) : 𝟭 (DerivedCategory A) ⟶ F n :=
    (rightUnitorNatIso _).inv ≫ (tensoringRight _).map
      (Functor.LaxMonoidal.ε DerivedCategory.Q ≫ DerivedCategory.Q.map
        ((HomologicalComplex.single _ (.up ℤ) 0).map (ι n)))
  let I := CochainComplex.ιKFlat A
  let L := I ⋙ DerivedCategory.Q
  have : L.IsLocalization (HomologicalComplex.quasiIso A (.up ℤ)).WKFlat :=
    inferInstanceAs (((HomologicalComplex.quasiIso A
      (.up ℤ)).localizerMorphismKFlat.functor ⋙ DerivedCategory.Q).IsLocalization _)
  let v (n : ℕ) : L ⋙ F n ⟶
      I ⋙ (tensorRight (B n)).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    Functor.whiskerLeft I (tensorComparison (B n))
  let w (n : ℕ) : L ⋙ G n ⟶
      I ⋙ (tensorRight (B n)).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    Functor.whiskerLeft I (c n)
  have hv (n : ℕ) : IsIso (v n) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro P
    exact tensorComparison_isIso (B n) P.obj P.property
  have hw (n : ℕ) : IsIso (w n) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro P
    exact hc n P.obj P.property
  have result : ∃ en : ∀ n, F n ≅ G n,
      (∀ n K, (t n).app K ≫ (en n).hom.app K =
        (en (n + 1)).hom.app K ≫ (s n).app K) ∧
      (∀ n K, (a n).app K ≫ (en n).hom.app K = (b n).app K) := by
    refine descend_comparison L
      (HomologicalComplex.quasiIso A (.up ℤ)).WKFlat F G
      (fun n ↦ I ⋙ (tensorRight (B n)).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
      v w t s a b
      (fun n P ↦ DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex ((tensoringRight A).map (τ n))
          (.up ℤ)).app P.obj))
      (fun n P ↦ DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
        ((rightUnitorNatIso A).inv ≫ (tensoringRight A).map (ι n)) (.up ℤ)).app P.obj))
      ?_ ?_ ?_ ?_
    · intro n P
      exact tensorComparison_step (τ n) P.obj
    · intro n P
      exact hs n P.obj
    · intro n P
      exact tensorComparison_unit (B n) (ι n) P.obj
    · intro n P
      exact hu n P.obj
  exact result

end PrincipalTensorAux

end

/-- Derived tensor with the degree-zero coefficient modules is naturally the
restricted derived scalar extension, preserving the canonical transitions and units.
Source: the balanced tensor computation and localization argument of
`lem-pe-internal-kflat-scalar-tower-realization`.
(auxiliary; not a blueprint node).
Proof: compare both functors with termwise tensor on K-flat complexes, using the
lax tensorator and natural_computation. Their component isomorphisms intertwine
transitions and units. Fully faithful precomposition with the localization of
K-flat complexes descends the isomorphism and the two equations. -/
theorem derived_realization
    (eB : ∀ n, B n ≅ (Mod.comap (q n)).obj (Mod.regular (S n)))
    (hι : ∀ n, (ι n).hom ≫ (eB n).hom.hom = q n)
    (hτ : ∀ n, (τ n).hom ≫ (eB n).hom.hom = (eB (n + 1)).hom.hom ≫ r n) :
    ∃ e : ∀ n, tensorRight ((DerivedCategory.singleFunctor (Mod C R) 0).obj (B n)) ≅
        reduction R S q n ⋙ restriction R S q n,
      (∀ n K, (K ◁ (DerivedCategory.singleFunctor (Mod C R) 0).map (τ n)) ≫
        (e n).hom.app K = (e (n + 1)).hom.app K ≫ step R S q r h K n) ∧
      (∀ n K, ((ρ_ K).inv ≫ K ◁
          (Functor.LaxMonoidal.ε DerivedCategory.Q ≫ DerivedCategory.Q.map
            ((HomologicalComplex.single (Mod C R) (.up ℤ) 0).map (ι n)))) ≫
        (e n).hom.app K =
          (Mod.derivedExtendMapDerivedCategoryAdjunction (q n)).unit.app K) := by
  obtain ⟨c, hc, hs, hu⟩ := natural_computation R S q r h B ι τ eB hι hτ
  let G (n : ℕ) := reduction R S q n ⋙ restriction R S q n
  let s (n : ℕ) : G (n + 1) ⟶ G n :=
    { app := fun K ↦ step R S q r h K n
      naturality := by
        intro X Y f
        dsimp only [G, Functor.comp_map, step]
        simpa only [Category.assoc] using towerStep_naturality
          (Mod.derivedExtendMapDerivedCategoryAdjunction (r n))
          (association R S q r h n) (restrictionComp R S q r h n) f }
  exact PrincipalTensorAux.realize B ι τ G s
    (fun n ↦ (Mod.derivedExtendMapDerivedCategoryAdjunction (q n)).unit) c hc hs hu

end CategoryTheory.Mod.KFlatScalarTower

namespace CategoryTheory.Mod.KFlatScalarTower

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory MonoidalCategory MonObj Limits
open scoped CategoryTheory.Obj

private theorem realizeTransport
    {D : Type u} [Category.{v} D]
    (F : ℕ → D ⥤ D) (t : ∀ n, F (n + 1) ⟶ F n)
    (unit : ∀ n, 𝟭 D ⟶ F n)
    {O K : D} (e : O ≅ K)
    (V : ℕ → D) (d : ∀ n, V (n + 1) ⟶ V n) (c : ∀ n, O ⟶ V n)
    (m : ∀ n, (F n).obj O ≅ V n)
    (hd : ∀ n, (t n).app O ≫ (m n).hom = (m (n + 1)).hom ≫ d n)
    (hc : ∀ n, (unit n).app O ≫ (m n).hom = c n) :
    ∃ en : ∀ n, V n ≅ (F n).obj K,
      (∀ n, d n ≫ (en n).hom = (en (n + 1)).hom ≫ (t n).app K) ∧
      (∀ n, c n ≫ (en n).hom = e.hom ≫ (unit n).app K) := by
  let en (n : ℕ) : V n ≅ (F n).obj K := (m n).symm ≪≫ (F n).mapIso e
  refine ⟨en, ?_, ?_⟩
  · intro n
    apply (cancel_epi (m (n + 1)).hom).mp
    simp only [en, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc,
      Iso.hom_inv_id_assoc]
    rw [← reassoc_of% (hd n), Iso.hom_inv_id_assoc]
    exact ((t n).naturality e.hom).symm
  · intro n
    simp only [en, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
    rw [← hc n, Category.assoc, Iso.hom_inv_id_assoc]
    exact ((unit n).naturality e.hom).symm

end

end CategoryTheory.Mod.KFlatScalarTower

namespace CategoryTheory.Mod.KFlatScalarTower

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory MonoidalCategory MonObj Limits
open scoped CategoryTheory.Obj
variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C]
  [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
  [IsGrothendieckAbelian.{v} C] [Abelian.HasFunctorialFlatResolution C]
  (R : C) [MonObj R] [IsCommMonObj R]
  (S : ℕ → C) [∀ n, MonObj (S n)] [∀ n, IsCommMonObj (S n)]
  (q : ∀ n, R ⟶ S n) [∀ n, IsMonHom (q n)]
  (r : ∀ n, S (n + 1) ⟶ S n) [∀ n, IsMonHom (r n)]
  (h : ∀ n, q (n + 1) ≫ r n = q n)
variable (B : ℕ → Mod C R) (ι : ∀ n, 𝟙_ (Mod C R) ⟶ B n)
  (τ : ∀ n, B (n + 1) ⟶ B n)

/-- Native K-flat complexes realize a coherent tower of derived scalar extensions,
including its canonical units.

Source: Stacks Project, Tags 064K and 06XY; the scalar-realization argument of
`lem-pe-kflat-scalar-tower-realization`, in internal module objects
(blueprint: lem-pe-internal-kflat-scalar-tower-realization).

Proof: the coequalizers defining extension of scalars and tensor with the restricted
regular module are the same coequalizer. Its comparison is linear for the common
ring; the action equations follow after precomposition with the epimorphic tensor
projection. Compose this comparison with the braiding and with `eB`.
The counit computing derived extension on a native K-flat complex is invertible.
Exact restriction commutes with localization, so this counit gives the claimed
level isomorphisms. The ordinary extension-restriction unit becomes the right
unitor inverse followed by tensoring `ι`, by `hι`. Naturality of derived adjunctions
therefore gives the second displayed identity. For transitions, `hτ` identifies
the ordinary scalar-change morphism with tensoring `τ`. Take its adjunction mate.
The quotient-factor equality `h` identifies the composite restriction, and
uniqueness of left adjoints identifies its mate with `association`. Thus the first
identity uses exactly `step`, including its specified associator. Finally transport
all level isomorphisms along `eP`; naturality preserves both identities.

The argument applies also to the zero complex and to a zero coefficient ring;
neither flat terms nor a nonzero coefficient object is required. -/
theorem realization
    (eB : ∀ n, B n ≅ (Mod.comap (q n)).obj (Mod.regular (S n)))
    (hι : ∀ n, (ι n).hom ≫ (eB n).hom.hom = q n)
    (hτ : ∀ n, (τ n).hom ≫ (eB n).hom.hom = (eB (n + 1)).hom.hom ≫ r n)
    (K : DerivedCategory (Mod C R)) (P : CochainComplex (Mod C R) ℤ)
    (hP : (HomologicalComplex.quasiIso (Mod C R) (.up ℤ)).kFlat P)
    (eP : DerivedCategory.Q.obj P ≅ K) :
    ∃ e : ∀ n, DerivedCategory.Q.obj ((tensorLevel R B n).obj P) ≅
        (restriction R S q n).obj ((reduction R S q n).obj K),
      (∀ n, DerivedCategory.Q.map (tensorStep R B τ P n) ≫ (e n).hom =
        (e (n + 1)).hom ≫ step R S q r h K n) ∧
      (∀ n, DerivedCategory.Q.map (tensorUnit R B ι P n) ≫ (e n).hom =
        eP.hom ≫ (Mod.derivedExtendMapDerivedCategoryAdjunction (q n)).unit.app K) := by
  obtain ⟨c, hc, hs, hu⟩ := natural_computation R S q r h B ι τ eB hι hτ
  let F (n : ℕ) := reduction R S q n ⋙ restriction R S q n
  let t (n : ℕ) : F (n + 1) ⟶ F n :=
    { app := fun K ↦ step R S q r h K n
      naturality := by
        intro X Y f
        dsimp only [F, Functor.comp_map, step]
        simpa only [Category.assoc] using towerStep_naturality
          (Mod.derivedExtendMapDerivedCategoryAdjunction (r n))
          (association R S q r h n) (restrictionComp R S q r h n) f }
  have (n : ℕ) : IsIso ((c n).app P) := hc n P hP
  exact realizeTransport F t
    (fun n ↦ (Mod.derivedExtendMapDerivedCategoryAdjunction (q n)).unit) eP
    (fun n ↦ DerivedCategory.Q.obj ((tensorLevel R B n).obj P))
    (fun n ↦ DerivedCategory.Q.map (tensorStep R B τ P n))
    (fun n ↦ DerivedCategory.Q.map (tensorUnit R B ι P n))
    (fun n ↦ asIso ((c n).app P)) (fun n ↦ hs n P) (fun n ↦ hu n P)

end

end CategoryTheory.Mod.KFlatScalarTower
