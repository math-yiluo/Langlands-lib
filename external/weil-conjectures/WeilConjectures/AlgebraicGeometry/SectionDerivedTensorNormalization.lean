/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.SectionDerivedPushpullNormalization
public import WeilConjectures.AlgebraicGeometry.SectionTotalOplaxComparisonData
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import Mathlib.Algebra.Homology.Localization
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.Logic.Small.Defs
import all WeilConjectures.AlgebraicGeometry.ProEtaleSectionModuleFunctors
import all Mathlib.Algebra.Homology.Localization
import all Mathlib.CategoryTheory.Limits.HasLimits
import all Mathlib.Logic.Small.Defs
import WeilConjectures.AlgebraicGeometry.SectionDerivedRepresentativeSquare
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.MonoidalTensorCounit

/-! # Derived tensor normalization under the section equivalence

Source: Stacks Project, Cohomology on Sites, Tag 07A4,
`lemma-pullback-tensor-product`; Tags 06YU and 0G7E; Modules on Sites, Tag 03EL
(auxiliary; not a blueprint node).

The statement compares the specified localization, tensor, unit and pullback maps.
Its helper definitions expose existing transported constraints and the localized
scalar-multiplication unit. All complexes and derived inputs are unbounded.
-/

@[expose] public noncomputable section
set_option linter.all false
set_option linter.mathlibStandardSet false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u u₁ v₁ u₂ v₂
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
attribute [local instance] AlgebraicGeometry.ProEtale.CondensedRing.projectionDerivedMonoidal
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleAbelian
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleMonoidal
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleHasDerived
  AlgebraicGeometry.ProEtale.CondensedRing.projectionSheafMonoidal
  AlgebraicGeometry.ProEtale.CondensedRing.projectionCoefficientMonObj
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleCategory

namespace AlgebraicGeometry.ProEtale.ModuleRingedComparison
/-- Associator and unitor compatibility for a specified tensor comparison.
Source: Stacks 06YU and 07A4 (auxiliary; not a blueprint node). -/
def TensorConstraintCondition
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (F : C ⥤ D) (B : C × C ⥤ C) (T : D × D ⥤ D) (I : C) (J : D)
    (a : ∀ M N P : C, B.obj (B.obj (M, N), P) ≅ B.obj (M, B.obj (N, P)))
    (l : ∀ M : C, B.obj (I, M) ≅ M) (r : ∀ M : C, B.obj (M, I) ≅ M)
    (a' : ∀ M N P : D, T.obj (T.obj (M, N), P) ≅ T.obj (M, T.obj (N, P)))
    (l' : ∀ M : D, T.obj (J, M) ≅ M) (r' : ∀ M : D, T.obj (M, J) ≅ M)
    (d : B ⋙ F ⟶ (F.prod F) ⋙ T) (e : F.obj I ⟶ J) : Prop :=
  (∀ M N P : C,
    F.map (a M N P).hom ≫ d.app (M, B.obj (N, P)) ≫
        T.map (Prod.mkHom (𝟙 (F.obj M)) (d.app (N, P))) =
      d.app (B.obj (M, N), P) ≫ T.map (Prod.mkHom (d.app (M, N)) (𝟙 (F.obj P))) ≫
        (a' (F.obj M) (F.obj N) (F.obj P)).hom) ∧
  (∀ M : C, d.app (I, M) ≫ T.map (Prod.mkHom e (𝟙 (F.obj M))) ≫
      (l' (F.obj M)).hom = F.map (l M).hom) ∧
  (∀ M : C, d.app (M, I) ≫ T.map (Prod.mkHom (𝟙 (F.obj M)) e) ≫
      (r' (F.obj M)).hom = F.map (r M).hom)

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
  [∀ X : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ X)]
/-- The associator of the existing conjugate tensor, with the equivalence fixed.
Source: Stacks 06YU (auxiliary; not a blueprint node). -/
def normalizationDerivedAssociator (T : Scheme.{u})
    (M N P : DerivedCategory (modules Λ T)) :
    (tensor Λ T).obj ((tensor Λ T).obj (M, N), P) ≅
      (tensor Λ T).obj (M, (tensor Λ T).obj (N, P)) :=
  @MonoidalCategoryStruct.associator _ _
    (Monoidal.transportStruct (derivedEquivalence Λ T)) M N P

/-- The left unitor of the existing conjugate tensor.
Source: Stacks 06YU (auxiliary; not a blueprint node). -/
def normalizationDerivedLeftUnitor (T : Scheme.{u}) (M : DerivedCategory (modules Λ T)) :
    (tensor Λ T).obj (tensorUnit Λ T, M) ≅ M :=
  cast (by rfl) (@MonoidalCategoryStruct.leftUnitor _ _
    (Monoidal.transportStruct (derivedEquivalence Λ T)) M)

/-- The right unitor of the existing conjugate tensor.
Source: Stacks 06YU (auxiliary; not a blueprint node). -/
def normalizationDerivedRightUnitor (T : Scheme.{u}) (M : DerivedCategory (modules Λ T)) :
    (tensor Λ T).obj (M, tensorUnit Λ T) ≅ M :=
  cast (by rfl) (@MonoidalCategoryStruct.rightUnitor _ _
    (Monoidal.transportStruct (derivedEquivalence Λ T)) M)

/-- The regular-module unit comparison, obtained from localization and the ordinary unit.
Source: Stacks 06YU (auxiliary; not a blueprint node). -/
def normalizationDerivedRegularUnit (T : Scheme.{u}) :
    tensorUnit Λ T ≅ (DerivedCategory.singleFunctor (modules Λ T) 0).obj
      (𝟙_ (modules Λ T)) :=
  sectionLocalizationComparison Λ T (𝟙_ (CochainComplex (internalModules Λ T) ℤ)) ≪≫
    DerivedCategory.Q.mapIso (totalUnitComparison Λ T)

/-- The ringed derived unit map, localizing the actual scalar-multiplication unit.
Source: Stacks 03EL and 07A4 (auxiliary; not a blueprint node). -/
def normalizationDerivedSectionUnit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (derivedPullback Λ f).obj (tensorUnit Λ Y) ⟶ tensorUnit Λ X :=
  (derivedPullback Λ f).map (normalizationDerivedRegularUnit Λ Y).hom ≫
    (pullback Λ f).mapDerivedCategoryFactors.hom.app
      (𝟙_ (CochainComplex (modules Λ Y) ℤ)) ≫
    DerivedCategory.Q.map (sectionTotalUnit Λ f) ≫
    (normalizationDerivedRegularUnit Λ X).inv

set_option backward.isDefEq.respectTransparency false in
/-- The inverse of the actual localized internal oplax transformation.
Source: Stacks 07A4 (auxiliary; not a blueprint node). -/
def normalizationDerivedInternalMu {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ((((Functor.whiskeringLeft₂ _).obj (internalDerivedPullback Λ f)).obj
      (internalDerivedPullback Λ f)).obj (CondensedRing.derivedTensor Λ X)) ⟶
    (Functor.postcompose₂.obj (internalDerivedPullback Λ f)).obj
      (CondensedRing.derivedTensor Λ Y) :=
  inv ((CondensedRing.upperStar Λ f).leftDerivedTensorComparison)

/-- The actual internal derived unit comparison, with its functor fixed explicitly.
Source: Stacks 07A4 (auxiliary; not a blueprint node). -/
def normalizationDerivedInternalUnit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (internalDerivedPullback Λ f).obj (𝟙_ (DerivedCategory (internalModules Λ Y))) ≅
      𝟙_ (DerivedCategory (internalModules Λ X)) :=
  CondensedRing.leftDerivedUpperStarUnitIso Λ f

set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] tensorComparison tensorPullComparison derivedPullComparison qTensor
  CategoryTheory.Mod.monoidalClosed CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.leftDerivedTensorComparison
  CategoryTheory.Functor.leftDerivedFunctorCounit
  internalPullMonoidal CondensedRing.monoidal_upperStar

private def uncurryPostIso
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {E : Type u} [Category E]
    (B : C ⥤ C ⥤ D) (F : D ⥤ E) :
    Functor.uncurry.obj B ⋙ F ≅
      Functor.uncurry.obj ((Functor.postcompose₂.obj F).obj B) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro M N k
    simp [Functor.uncurry, Functor.map_comp])

section GenericSquare
variable {C₁ C₂ D₁ D₂ : Type*}
  [Category C₁] [Category C₂] [Category D₁] [Category D₂]
  (B₁ : C₁ × C₁ ⥤ C₁) (B₂ : C₂ × C₂ ⥤ C₂)
  (e : C₁ ≌ D₁) (H : C₂ ⥤ D₂) (F : C₁ ⥤ C₂) (L : D₁ ⥤ D₂)
  (TY : D₁ × D₁ ⥤ D₁) (TX : D₂ × D₂ ⥤ D₂)
  (θY : B₁ ⋙ e.functor ≅
    (e.functor.prod e.functor) ⋙ TY)
  (θX : B₂ ⋙ H ≅ (H.prod H) ⋙ TX)
  (γ : F ⋙ H ≅ e.functor ⋙ L)
  (di : B₁ ⋙ F ≅
    (F.prod F) ⋙ B₂)
  (d : TY ⋙ L ≅ (L.prod L) ⋙ TX)

private def conjugatedIso :
    TY ⋙ L ≅
      ((L).prod (L)) ⋙ TX := by
  let G := e.inverse
  let E := H
  let a := e.counitIso
  exact
    Functor.isoWhiskerRight
      (Functor.isoWhiskerRight (NatIso.prod a.symm a.symm) (TY)) L ≪≫
    Functor.isoWhiskerLeft (G.prod G)
      (Functor.isoWhiskerRight (θY).symm L) ≪≫
    Functor.isoWhiskerLeft ((G.prod G) ⋙
      B₁)
      (γ).symm ≪≫
    Functor.isoWhiskerLeft (G.prod G) (Functor.isoWhiskerRight di E) ≪≫
    Functor.isoWhiskerLeft ((G.prod G) ⋙ (F.prod F)) (θX) ≪≫
    Functor.isoWhiskerLeft (G.prod G)
      (Functor.isoWhiskerRight
        (NatIso.prod (γ) (γ))
        (TX)) ≪≫
    Functor.isoWhiskerRight
      (NatIso.prod (Functor.isoWhiskerRight a L) (Functor.isoWhiskerRight a L))
      (TX)

private theorem conjugatedIso_hom (M N : D₁) :
    (conjugatedIso B₁ B₂ e H F L TY TX θY θX γ di).hom.app (M, N) =
      L.map (TY.map (Prod.mkHom (e.counitIso.inv.app M) (e.counitIso.inv.app N))) ≫
      L.map (θY.inv.app (e.inverse.obj M, e.inverse.obj N)) ≫
      γ.inv.app (B₁.obj (e.inverse.obj M, e.inverse.obj N)) ≫
      H.map (di.hom.app (e.inverse.obj M, e.inverse.obj N)) ≫
      θX.hom.app (F.obj (e.inverse.obj M), F.obj (e.inverse.obj N)) ≫
      TX.map (Prod.mkHom (γ.hom.app (e.inverse.obj M)) (γ.hom.app (e.inverse.obj N))) ≫
      TX.map (Prod.mkHom (L.map (e.counitIso.hom.app M))
        (L.map (e.counitIso.hom.app N))) := by
  rfl

private def genericSquareLeft :
    B₁ ⋙
        F ⋙ H ≅
      (e.functor.prod e.functor) ⋙
        ((L).prod (L)) ⋙ TX := by
  exact Functor.isoWhiskerRight di H ≪≫
    Functor.isoWhiskerLeft
      ((F).prod (F))
      (θX) ≪≫
    Functor.isoWhiskerRight
      (NatIso.prod (γ) (γ)) (TX)

private def genericSquareRight :
    B₁ ⋙
        F ⋙ H ≅
      (e.functor.prod e.functor) ⋙
        ((L).prod (L)) ⋙ TX :=
  Functor.isoWhiskerLeft (B₁)
      (γ) ≪≫
    Functor.isoWhiskerRight (θY) (L) ≪≫
    Functor.isoWhiskerLeft
      (e.functor.prod e.functor)
      (d)

private instance isIso_prod_mkHom
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {M N : C} {P Q : D} (a : M ⟶ N) (b : P ⟶ Q) [IsIso a] [IsIso b] :
    IsIso (Prod.mkHom a b) :=
  (isIso_prod_iff _ _).mpr ⟨inferInstance, inferInstance⟩

private theorem genericSquare_eq
    (ha : conjugatedIso B₁ B₂ e H F L TY TX θY θX γ di = d) :
    genericSquareLeft B₁ B₂ e H F L TX θX γ di = genericSquareRight B₁ e H F L TY TX θY γ d := by
  have : (e.inverse.prod
      e.inverse).IsEquivalence :=
    (e.symm.prod e.symm).isEquivalence_functor
  apply Iso.ext
  apply ((Functor.whiskeringLeft _ _ _).obj
    (e.inverse.prod e.inverse)).map_injective
  ext ⟨M, N⟩
  change (genericSquareLeft B₁ B₂ e H F L TX θX γ di).hom.app
    (e.inverse.obj M, e.inverse.obj N) =
    (genericSquareRight B₁ e H F L TY TX θY γ d).hom.app
      (e.inverse.obj M, e.inverse.obj N)
  let E := e
  let V := TX
  let c := E.counitIso
  let p := L.map ((TY).map (Prod.mkHom (c.inv.app M) (c.inv.app N))) ≫
    L.map ((θY).inv.app (E.inverse.obj M, E.inverse.obj N)) ≫
    (γ).inv.app (B₁.obj (E.inverse.obj M, E.inverse.obj N))
  let z := V.map (Prod.mkHom (L.map (c.hom.app M)) (L.map (c.hom.app N)))
  have : IsIso p := by dsimp [p]; infer_instance
  have : IsIso z := by dsimp [z]; infer_instance
  apply (cancel_epi p).1
  apply (cancel_mono z).1
  have h := NatTrans.congr_app (congrArg Iso.hom ha) (M, N)
  have hl : p ≫ (genericSquareLeft B₁ B₂ e H F L TX θX γ di).hom.app
      (E.inverse.obj M, E.inverse.obj N) ≫ z =
      (conjugatedIso B₁ B₂ e H F L TY TX θY θX γ di).hom.app (M, N) := by
    simp only [p, z, E, V, c, genericSquareLeft, conjugatedIso, Iso.trans_hom,
      NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.assoc]
    rfl
  have hr : p ≫ (genericSquareRight B₁ e H F L TY TX θY γ d).hom.app
      (E.inverse.obj M, E.inverse.obj N) ≫ z =
      (d).hom.app (M, N) := by
    dsimp only [p, z, genericSquareRight]
    simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
      Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Category.assoc, Iso.inv_hom_id_app_assoc, ← Functor.map_comp_assoc,
      Iso.inv_hom_id_app]
    have hn := (d).hom.naturality
      (Prod.mkHom (c.hom.app M) (c.hom.app N))
    simp only [Functor.map_comp, Category.assoc]
    change L.map ((TY).map (Prod.mkHom (c.hom.app M) (c.hom.app N))) ≫
      (d).hom.app (M, N) =
      (d).hom.app (E.functor.obj (E.inverse.obj M),
        E.functor.obj (E.inverse.obj N)) ≫
      V.map (Prod.mkHom (L.map (c.hom.app M)) (L.map (c.hom.app N))) at hn
    erw [CategoryTheory.Functor.map_id, Category.id_comp, ← hn]
    simp only [← Functor.map_comp_assoc, ← Functor.map_comp, prod_comp,
      Iso.inv_hom_id_app, ← prod_id, CategoryTheory.Functor.map_id, Category.id_comp]
  simpa only [Category.assoc] using hl.trans (h.trans hr.symm)

private theorem genericSquare_hom
    (h : genericSquareLeft B₁ B₂ e H F L TX θX γ di =
      genericSquareRight B₁ e H F L TY TX θY γ d) (M N : C₁) :
    H.map (di.hom.app (M, N)) ≫ θX.hom.app (F.obj M, F.obj N) ≫
      TX.map (Prod.mkHom (γ.hom.app M) (γ.hom.app N)) =
        γ.hom.app (B₁.obj (M, N)) ≫ L.map (θY.hom.app (M, N)) ≫
          d.hom.app (e.functor.obj M, e.functor.obj N) := by
  exact NatTrans.congr_app (congrArg Iso.hom h) (M, N)

private theorem genericSquare_inv
    (h : genericSquareLeft B₁ B₂ e H F L TX θX γ di =
      genericSquareRight B₁ e H F L TY TX θY γ d) (M N : C₁) :
    TX.map (Prod.mkHom (γ.inv.app M) (γ.inv.app N)) ≫
      θX.inv.app (F.obj M, F.obj N) ≫ H.map (di.inv.app (M, N)) =
        d.inv.app (e.functor.obj M, e.functor.obj N) ≫ L.map (θY.inv.app (M, N)) ≫
          γ.inv.app (B₁.obj (M, N)) := by
  simpa only [genericSquareLeft, genericSquareRight, Iso.trans_inv,
    NatTrans.comp_app, Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, NatIso.prod, NatTrans.prod,
    Functor.prod_obj, Category.assoc]
      using NatTrans.congr_app (congrArg Iso.inv h) (M, N)

end GenericSquare

private def tensorIsoFromCurried {C D : Type*} [Category C] [Category D]
    (B : C ⥤ C ⥤ C) (T : D ⥤ D ⥤ D) (F : C ⥤ D)
    (δ : (Functor.postcompose₂.obj F).obj B ⟶
      (((Functor.whiskeringLeft₂ D).obj F).obj F).obj T) [IsIso δ] :
    Functor.uncurry.obj B ⋙ F ≅ (F.prod F) ⋙ Functor.uncurry.obj T :=
  uncurryPostIso B F ≪≫ Functor.uncurry.mapIso (asIso δ)

private theorem tensorIsoFromCurried_hom {C D : Type*} [Category C] [Category D]
    (B : C ⥤ C ⥤ C) (T : D ⥤ D ⥤ D) (F : C ⥤ D)
    (δ : (Functor.postcompose₂.obj F).obj B ⟶
      (((Functor.whiskeringLeft₂ D).obj F).obj F).obj T) [IsIso δ] (M N : C) :
    (tensorIsoFromCurried B T F δ).hom.app (M, N) = (δ.app M).app N := by
  simp only [tensorIsoFromCurried, uncurryPostIso, Iso.trans_hom,
    NatTrans.comp_app, NatIso.ofComponents_hom_app, Iso.refl_hom, Category.id_comp]
  rfl

private theorem tensorIsoFromCurried_inv {C D : Type*} [Category C] [Category D]
    (B : C ⥤ C ⥤ C) (T : D ⥤ D ⥤ D) (F : C ⥤ D)
    (δ : (Functor.postcompose₂.obj F).obj B ⟶
      (((Functor.whiskeringLeft₂ D).obj F).obj F).obj T) [IsIso δ] (M N : C) :
    (tensorIsoFromCurried B T F δ).inv.app (M, N) = ((inv δ).app M).app N := by
  simp only [tensorIsoFromCurried, uncurryPostIso, Iso.trans_inv,
    NatTrans.comp_app, NatIso.ofComponents_inv_app, Iso.refl_inv]
  erw [Category.comp_id]
  rfl

private def internalTensorIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Functor.uncurry.obj (CondensedRing.derivedTensor Λ Y) ⋙ internalDerivedPullback Λ f ≅
      ((internalDerivedPullback Λ f).prod (internalDerivedPullback Λ f)) ⋙
        Functor.uncurry.obj (CondensedRing.derivedTensor Λ X) := by
  have : IsIso (internalDelta Λ f) := by
    dsimp only [internalDelta]
    infer_instance
  exact tensorIsoFromCurried (CondensedRing.derivedTensor Λ Y)
    (CondensedRing.derivedTensor Λ X) (internalDerivedPullback Λ f) (internalDelta Λ f)

omit [∀ X : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ X)] in
private theorem internalTensorIso_hom {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M N : DerivedCategory (internalModules Λ Y)) :
    (internalTensorIso Λ f).hom.app (M, N) = ((internalDelta Λ f).app M).app N := by
  have : IsIso (internalDelta Λ f) := by
    dsimp only [internalDelta]
    infer_instance
  exact tensorIsoFromCurried_hom (CondensedRing.derivedTensor Λ Y)
    (CondensedRing.derivedTensor Λ X) (internalDerivedPullback Λ f) (internalDelta Λ f) M N

private theorem inverse_eq_of_eq {C : Type*} [Category C] {A B : C}
    (a b : A ⟶ B) [IsIso a] [IsIso b] (h : a = b) : inv a = inv b := by
  subst b
  rfl

omit [∀ X : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ X)] in
private theorem ordinaryMonoidal_eq {X Y : Scheme.{u}} (f : X ⟶ Y) :
    internalPullMonoidal Λ f = CondensedRing.monoidal_upperStar Λ f := by
  apply Functor.Monoidal.toOplaxMonoidal_injective
  unfold internalPullMonoidal
  exact internalPullOplax_eq_canonical Λ f

omit [∀ X : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ X)] in
private theorem internalDelta_eq_canonical {X Y : Scheme.{u}} (f : X ⟶ Y) :
    internalDelta Λ f =
      (letI := CondensedRing.monoidal_upperStar Λ f
       (CondensedRing.upperStar Λ f).leftDerivedTensorComparison) := by
  unfold internalDelta
  rw [ordinaryMonoidal_eq]

omit [∀ X : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ X)] in
private theorem internalTensorIso_inv {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M N : DerivedCategory (internalModules Λ Y)) :
    (internalTensorIso Λ f).inv.app (M, N) =
      ((normalizationDerivedInternalMu Λ f).app M).app N := by
  have : IsIso (internalDelta Λ f) := by
    dsimp only [internalDelta]
    infer_instance
  have h := tensorIsoFromCurried_inv (CondensedRing.derivedTensor Λ Y)
    (CondensedRing.derivedTensor Λ X) (internalDerivedPullback Λ f) (internalDelta Λ f) M N
  change (internalTensorIso Λ f).inv.app (M, N) = _ at h
  rw [h]
  have hd := internalDelta_eq_canonical Λ f
  have hi := inverse_eq_of_eq _ _ hd
  change inv (internalDelta Λ f) = normalizationDerivedInternalMu Λ f at hi
  exact congrArg (fun k ↦ (k.app M).app N) hi

private def actualComparisonIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    tensor Λ Y ⋙ derivedPullback Λ f ≅
      ((derivedPullback Λ f).prod (derivedPullback Λ f)) ⋙ tensor Λ X :=
  conjugatedIso (Functor.uncurry.obj (CondensedRing.derivedTensor Λ Y))
    (Functor.uncurry.obj (CondensedRing.derivedTensor Λ X))
    (derivedEquivalence Λ Y) (derivedEquivalence Λ X).functor
    (internalDerivedPullback Λ f) (derivedPullback Λ f) (tensor Λ Y) (tensor Λ X)
    (tensorComparison Λ Y) (tensorComparison Λ X) (derivedPullComparison Λ f)
    (internalTensorIso Λ f)

private theorem actualComparisonIso_hom {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M N : DerivedCategory (modules Λ Y)) :
    (actualComparisonIso Λ f).hom.app (M, N) =
      DerivedRepresentativeSquare.actualTensor Λ f M N := by
  have h := conjugatedIso_hom (Functor.uncurry.obj (CondensedRing.derivedTensor Λ Y))
    (Functor.uncurry.obj (CondensedRing.derivedTensor Λ X))
    (derivedEquivalence Λ Y) (derivedEquivalence Λ X).functor
    (internalDerivedPullback Λ f) (derivedPullback Λ f) (tensor Λ Y) (tensor Λ X)
    (tensorComparison Λ Y) (tensorComparison Λ X) (derivedPullComparison Λ f)
    (internalTensorIso Λ f) M N
  simp only [internalTensorIso_hom] at h
  convert! h using 1 <;> rfl

private theorem totalPullComparison_eq {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P Q : CochainComplex (modules Λ Y) ℤ) :
    totalPullComparison Λ f P Q = (sectionTotalIso Λ f P Q).hom := by
  rw [sectionTotalIso_hom]
  unfold totalPullComparison
  simp only [eqToHom_refl, Functor.map_id, Category.id_comp, Category.comp_id]

attribute [local irreducible] normalizationDerivedRegularUnit normalizationDerivedSectionUnit
  normalizationDerivedInternalUnit normalizationDerivedInternalMu
attribute [local irreducible] actualComparisonIso

private theorem representative_equation {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P Q : CochainComplex (modules Λ Y) ℤ) :
    DerivedRepresentativeSquare.cochainPath Λ f P Q =
      (tensorPullComparison Λ f).hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
        DerivedRepresentativeSquare.output Λ f P Q := by
  have ht : TensorPullRepresentativeCondition Λ f (tensorPullComparison Λ f) := by
    unfold tensorPullComparison
    exact (tensorPullComparison_existsUnique Λ f).exists.choose_spec
  specialize ht P Q
  dsimp only [TensorPullRepresentativeCondition] at ht
  rw [totalPullComparison_eq] at ht
  dsimp only [DerivedRepresentativeSquare.cochainPath, DerivedRepresentativeSquare.input,
    DerivedRepresentativeSquare.output]
  convert! ht using 1 <;> first | exact Category.assoc _ _ _ | rfl

private theorem actualComparisonIso_eq {X Y : Scheme.{u}} (f : X ⟶ Y) :
    actualComparisonIso Λ f = tensorPullComparison Λ f := by
  obtain ⟨P, hP, _, _, hff⟩ :=
    SheafOfModules.site_derived_tensor_descent_independentCoefficients
      (Scheme.ProEt.topology Y) (ring Λ Y)
  apply Iso.ext
  apply (hff _ inferInstance _ _).1
  apply NatTrans.ext
  funext ⟨A, B⟩
  have hA : KFlatSectionComparison.sectionResolving Λ Y A.obj.as :=
    (hP A.obj).1 A.property
  have hB : KFlatSectionComparison.sectionResolving Λ Y B.obj.as :=
    (hP B.obj).1 B.property
  have hs := (DerivedRepresentativeSquare.section_derived_representative_square Λ f).1
    ⟨A.obj.as, hA⟩ ⟨B.obj.as, hB⟩
  have := hs.2.1
  apply (cancel_mono
    (DerivedRepresentativeSquare.output Λ f A.obj.as B.obj.as)).1
  change (actualComparisonIso Λ f).hom.app
    (DerivedCategory.Q.obj A.obj.as, DerivedCategory.Q.obj B.obj.as) ≫ _ = _
  rw [actualComparisonIso_hom]
  change DerivedRepresentativeSquare.actualPath Λ f A.obj.as B.obj.as = _
  rw [hs.2.2]
  exact representative_equation Λ f A.obj.as B.obj.as

private theorem regular_hom_eq (T : Scheme.{u}) :
    (DerivedRepresentativeSquare.regular Λ T).hom =
      (normalizationDerivedRegularUnit Λ T).hom := by
  unfold DerivedRepresentativeSquare.regular normalizationDerivedRegularUnit
  rfl

private theorem unit_normalization {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (derivedEquivalence Λ X).functor.map
        (normalizationDerivedInternalUnit Λ f).hom =
      (derivedPullComparison Λ f).hom.app (𝟙_ (DerivedCategory (internalModules Λ Y))) ≫
        normalizationDerivedSectionUnit Λ f := by
  have h := (DerivedRepresentativeSquare.section_derived_representative_square Λ f).2.2.2.1
  have h' := congrArg (fun k ↦
    (derivedPullComparison Λ f).hom.app (𝟙_ (DerivedCategory (internalModules Λ Y))) ≫
      (derivedPullback Λ f).map (DerivedRepresentativeSquare.regular Λ Y).hom ≫
        k ≫ (DerivedRepresentativeSquare.regular Λ X).inv) h
  dsimp only [tensorUnit] at h' ⊢
  with_unfolding_all simp only [DerivedRepresentativeSquare.actualUnit, cast_eq, Category.assoc,
    ← Functor.map_comp_assoc, Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp,
    Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app, Category.comp_id] at h'
  rw [regular_hom_eq] at h'
  have hi : (DerivedRepresentativeSquare.regular Λ X).inv =
      (normalizationDerivedRegularUnit Λ X).inv := by
    apply (cancel_epi (DerivedRepresentativeSquare.regular Λ X).hom).1
    rw [Iso.hom_inv_id, regular_hom_eq, Iso.hom_inv_id]
  rw [hi] at h'
  unfold normalizationDerivedInternalUnit normalizationDerivedSectionUnit
  exact h'

private def squareLeft {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Functor.uncurry.obj (CondensedRing.derivedTensor Λ Y) ⋙
      internalDerivedPullback Λ f ⋙ (derivedEquivalence Λ X).functor ≅
      ((derivedEquivalence Λ Y).functor.prod (derivedEquivalence Λ Y).functor) ⋙
        ((derivedPullback Λ f).prod (derivedPullback Λ f)) ⋙ tensor Λ X :=
  genericSquareLeft (Functor.uncurry.obj (CondensedRing.derivedTensor Λ Y))
    (Functor.uncurry.obj (CondensedRing.derivedTensor Λ X))
    (derivedEquivalence Λ Y) (derivedEquivalence Λ X).functor
    (internalDerivedPullback Λ f) (derivedPullback Λ f) (tensor Λ X)
    (tensorComparison Λ X) (derivedPullComparison Λ f) (internalTensorIso Λ f)

private def squareRight {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Functor.uncurry.obj (CondensedRing.derivedTensor Λ Y) ⋙
      internalDerivedPullback Λ f ⋙ (derivedEquivalence Λ X).functor ≅
      ((derivedEquivalence Λ Y).functor.prod (derivedEquivalence Λ Y).functor) ⋙
        ((derivedPullback Λ f).prod (derivedPullback Λ f)) ⋙ tensor Λ X :=
  genericSquareRight (Functor.uncurry.obj (CondensedRing.derivedTensor Λ Y))
    (derivedEquivalence Λ Y) (derivedEquivalence Λ X).functor
    (internalDerivedPullback Λ f) (derivedPullback Λ f) (tensor Λ Y) (tensor Λ X)
    (tensorComparison Λ Y) (derivedPullComparison Λ f) (tensorPullComparison Λ f)

private theorem square_eq {X Y : Scheme.{u}} (f : X ⟶ Y)
    (ha : actualComparisonIso Λ f = tensorPullComparison Λ f) :
    squareLeft Λ f = squareRight Λ f :=
  genericSquare_eq (Functor.uncurry.obj (CondensedRing.derivedTensor Λ Y))
    (Functor.uncurry.obj (CondensedRing.derivedTensor Λ X))
    (derivedEquivalence Λ Y) (derivedEquivalence Λ X).functor
    (internalDerivedPullback Λ f) (derivedPullback Λ f) (tensor Λ Y) (tensor Λ X)
    (tensorComparison Λ Y) (tensorComparison Λ X) (derivedPullComparison Λ f)
    (internalTensorIso Λ f) (tensorPullComparison Λ f) (by
      simpa only [actualComparisonIso] using ha)

attribute [local irreducible] conjugatedIso genericSquareLeft genericSquareRight
  internalTensorIso squareLeft squareRight

section GenericInternal
variable {C : Type u₁} [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
  [MonoidalClosed C] [BraidedCategory C] [Abelian.HasFunctorialFlatResolution C]
  {D : Type u₂} [Category.{u + 1} D] [Abelian D]
  [IsGrothendieckAbelian.{u + 1} D] [MonoidalCategory D] [MonoidalPreadditive D]
  [MonoidalClosed D] [BraidedCategory D] [Abelian.HasFunctorialFlatResolution D]
  (F : C ⥤ D) [F.Additive] [F.PreservesKFlatQuasiIso] [F.PreservesFlat]
  [F.IsLeftAdjoint] [F.Monoidal]

private theorem genericInternalWithUnit [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] :
    ∃ o : F.leftDerivedFunctor.OplaxMonoidal,
      (∀ M N, @Functor.OplaxMonoidal.δ _ _ _ _ _ _ F.leftDerivedFunctor o M N =
        (F.leftDerivedTensorComparison.app M).app N) ∧
      @Functor.OplaxMonoidal.η _ _ _ _ _ _ F.leftDerivedFunctor o =
        (F.leftDerivedTensorUnitIso).hom :=
  ⟨(F.leftDerivedMonoidalWithUnit).toOplaxMonoidal, (fun _ _ ↦ rfl), rfl⟩

end GenericInternal
include Λ in
private theorem internal_oplax_compatible {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃ o : (internalDerivedPullback Λ f).OplaxMonoidal,
      (∀ M N, @Functor.OplaxMonoidal.δ _ _ _ _ _ _ (internalDerivedPullback Λ f) o M N =
        ((internalDelta Λ f).app M).app N) ∧
      @Functor.OplaxMonoidal.η _ _ _ _ _ _ (internalDerivedPullback Λ f) o =
        (normalizationDerivedInternalUnit Λ f).hom := by
  dsimp only [internalDerivedPullback, comparisonSource]
  have hd := internalDelta_eq_canonical Λ f
  rw [hd]
  letI := CondensedRing.monoidal_upperStar Λ f
  obtain ⟨o, ho, he⟩ := genericInternalWithUnit (CondensedRing.upperStar Λ f)
  refine ⟨o, ho, ?_⟩
  erw [he]
  unfold Functor.leftDerivedTensorUnitIso normalizationDerivedInternalUnit
    CondensedRing.leftDerivedUpperStarUnitIso
  rfl

attribute [local irreducible] internalDelta internalDerivedPullback derivedPullback

private def nativeTensorIso {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] (e : C ≌ D) :
    letI := Monoidal.transport e
    (e.inverse.prod e.inverse) ⋙ Functor.uncurry.obj (curriedTensor C) ⋙ e.functor ≅
      Functor.uncurry.obj (curriedTensor D) := by
  letI := Monoidal.transport e
  refine NatIso.ofComponents (fun _ ↦ Iso.refl _) ?_
  intro A B f
  simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
  change e.functor.map (e.inverse.map f.1 ▷ e.inverse.obj A.2 ≫
    e.inverse.obj B.1 ◁ e.inverse.map f.2) =
    e.functor.map (e.inverse.map f.1 ▷ e.inverse.obj A.2) ≫
      e.functor.map (e.inverse.obj B.1 ◁ e.inverse.map f.2)
  exact e.functor.map_comp _ _

private theorem transportedTensor_map {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] (e : C ≌ D) {A B A' B' : D} (f : A ⟶ A') (g : B ⟶ B') :
    letI := Monoidal.transport e
    ((e.inverse.prod e.inverse) ⋙ Functor.uncurry.obj (curriedTensor C) ⋙ e.functor).map
      (Prod.mkHom f g) = f ⊗ₘ g := by
  letI := Monoidal.transport e
  change e.functor.map (e.inverse.map f ▷ e.inverse.obj B ≫
    e.inverse.obj A' ◁ e.inverse.map g) = e.functor.map (e.inverse.map f ⊗ₘ e.inverse.map g)
  rw [MonoidalCategory.tensorHom_def]

private def curryComparison {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D] (F : C ⥤ D)
    (d : Functor.uncurry.obj (curriedTensor C) ⋙ F ⟶
      (F.prod F) ⋙ Functor.uncurry.obj (curriedTensor D)) :
    (Functor.postcompose₂.obj F).obj (curriedTensor C) ⟶
      (((Functor.whiskeringLeft₂ D).obj F).obj F).obj (curriedTensor D) where
  app X :=
    { app := fun Y ↦ d.app (X, Y)
      naturality := by
        intro Y Z f
        have h := d.naturality (Prod.mkHom (𝟙 X) f)
        change F.map (𝟙 X ▷ Y ≫ X ◁ f) ≫ d.app (X, Z) =
          d.app (X, Y) ≫ (F.map (𝟙 X) ▷ F.obj Y ≫ F.obj X ◁ F.map f) at h
        simp only [id_whiskerRight, CategoryTheory.Functor.map_id] at h
        erw [Category.id_comp, Category.id_comp] at h
        exact h }
  naturality := by
    intro X Z f
    ext Y
    have h := d.naturality (Prod.mkHom f (𝟙 Y))
    change F.map (f ▷ Y ≫ Z ◁ 𝟙 Y) ≫ d.app (Z, Y) =
      d.app (X, Y) ≫ (F.map f ▷ F.obj Y ≫ F.obj Z ◁ F.map (𝟙 Y)) at h
    dsimp only [NatTrans.comp_app]
    convert! h using 1 <;>
      simp only [whiskerLeft_id, Category.comp_id, CategoryTheory.Functor.map_id] <;> rfl

private theorem square_for_lax {C₁ C₂ D₁ D₂ : Type*}
    [Category C₁] [Category C₂] [Category D₁] [Category D₂]
    [MonoidalCategory C₁] [MonoidalCategory C₂]
    [MonoidalCategory D₁] [MonoidalCategory D₂]
    (Q₁ : C₁ ⥤ D₁) (Q₂ : C₂ ⥤ D₂) [Q₁.Monoidal] [Q₂.Monoidal]
    (F : C₁ ⥤ C₂) [F.OplaxMonoidal] (G : D₁ ⥤ D₂)
    (γ : F ⋙ Q₂ ≅ Q₁ ⋙ G)
    (d : (Functor.postcompose₂.obj G).obj (curriedTensor D₁) ⟶
      (((Functor.whiskeringLeft₂ D₂).obj G).obj G).obj (curriedTensor D₂))
    (h : ∀ a b, Q₂.map (Functor.OplaxMonoidal.δ F a b) ≫
      Functor.OplaxMonoidal.δ Q₂ (F.obj a) (F.obj b) ≫
      (γ.hom.app a ⊗ₘ γ.hom.app b) = γ.hom.app (a ⊗ b) ≫
      G.map (Functor.OplaxMonoidal.δ Q₁ a b) ≫ (d.app (Q₁.obj a)).app (Q₁.obj b)) :
    ∀ a b, (d.app (Q₁.obj a)).app (Q₁.obj b) ≫
      (γ.inv.app a ⊗ₘ γ.inv.app b) ≫
      Functor.LaxMonoidal.μ Q₂ (F.obj a) (F.obj b) =
      G.map (Functor.LaxMonoidal.μ Q₁ a b) ≫ γ.inv.app (a ⊗ b) ≫
      Q₂.map (Functor.OplaxMonoidal.δ F a b) := by
  intro a b
  apply (cancel_mono (Functor.OplaxMonoidal.δ Q₂ (F.obj a) (F.obj b))).1
  simp only [Category.assoc, Functor.Monoidal.μ_δ, Category.comp_id]
  have hh := congrArg (fun k ↦ G.map (Functor.LaxMonoidal.μ Q₁ a b) ≫
    γ.inv.app (a ⊗ b) ≫ k ≫ (γ.inv.app a ⊗ₘ γ.inv.app b)) (h a b)
  simp only [Category.assoc, tensorHom_comp_tensorHom, Iso.hom_inv_id_app,
    id_tensorHom_id, Category.comp_id, Iso.inv_hom_id_app_assoc,
    Functor.Monoidal.μ_δ_map_assoc] at hh
  dsimp only [Functor.comp_obj] at hh
  change (d.app (Q₁.obj a)).app (Q₁.obj b) ≫ (γ.inv.app a ⊗ₘ γ.inv.app b) ≫ 𝟙 _ = _
  erw [Category.comp_id]
  erw [id_tensorHom_id, Category.comp_id] at hh
  exact hh.symm

@[instance_reducible]
private def squareOplax {C₁ C₂ D₁ D₂ : Type*}
    [Category C₁] [Category C₂] [Category D₁] [Category D₂]
    [MonoidalCategory C₁] [MonoidalCategory C₂]
    [MonoidalCategory D₁] [MonoidalCategory D₂]
    (Q₁ : C₁ ⥤ D₁) (Q₂ : C₂ ⥤ D₂) [Q₁.Monoidal] [Q₂.Monoidal] [Q₁.EssSurj]
    (F : C₁ ⥤ C₂) [F.OplaxMonoidal] (G : D₁ ⥤ D₂)
    (γ : F ⋙ Q₂ ≅ Q₁ ⋙ G)
    (d : (Functor.postcompose₂.obj G).obj (curriedTensor D₁) ⟶
      (((Functor.whiskeringLeft₂ D₂).obj G).obj G).obj (curriedTensor D₂))
    (h : ∀ a b, Q₂.map (Functor.OplaxMonoidal.δ F a b) ≫
      Functor.OplaxMonoidal.δ Q₂ (F.obj a) (F.obj b) ≫
      (γ.hom.app a ⊗ₘ γ.hom.app b) = γ.hom.app (a ⊗ b) ≫
      G.map (Functor.OplaxMonoidal.δ Q₁ a b) ≫ (d.app (Q₁.obj a)).app (Q₁.obj b)) :
    G.OplaxMonoidal :=
  Functor.OplaxMonoidal.ofLaxSquare (Q₁ := Q₁) (Q₂ := Q₂) (F := F) d
    (fun a ↦ γ.inv.app a) (fun _ _ f ↦ γ.inv.naturality f)
    (square_for_lax Q₁ Q₂ F G γ d h) (fun _ ↦ True)
    (fun X ↦ ⟨Q₁.objPreimage X, trivial, ⟨Q₁.objObjPreimageIso X⟩⟩)
    (fun _ _ _ ↦ inferInstance)

private theorem strongOfOplax {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D] (F : C ⥤ D) [F.OplaxMonoidal]
    [IsIso (Functor.OplaxMonoidal.η F)] [∀ M N, IsIso (Functor.OplaxMonoidal.δ F M N)] :
    ∃ m : F.Monoidal,
      (∀ M N, @Functor.OplaxMonoidal.δ _ _ _ _ _ _ F m.toOplaxMonoidal M N =
        Functor.OplaxMonoidal.δ F M N) ∧
      @Functor.OplaxMonoidal.η _ _ _ _ _ _ F m.toOplaxMonoidal =
        Functor.OplaxMonoidal.η F :=
  ⟨Functor.Monoidal.ofOplaxMonoidal F, (fun _ _ ↦ rfl), rfl⟩

private theorem squareOplaxData {C₁ C₂ D₁ D₂ : Type*}
    [Category C₁] [Category C₂] [Category D₁] [Category D₂]
    [MonoidalCategory C₁] [MonoidalCategory C₂]
    [MonoidalCategory D₁] [MonoidalCategory D₂]
    (Q₁ : C₁ ⥤ D₁) (Q₂ : C₂ ⥤ D₂) [Q₁.Monoidal] [Q₂.Monoidal] [Q₁.EssSurj]
    (F : C₁ ⥤ C₂) [F.OplaxMonoidal] (G : D₁ ⥤ D₂)
    (γ : F ⋙ Q₂ ≅ Q₁ ⋙ G)
    (d : (Functor.postcompose₂.obj G).obj (curriedTensor D₁) ⟶
      (((Functor.whiskeringLeft₂ D₂).obj G).obj G).obj (curriedTensor D₂))
    (h : ∀ a b, Q₂.map (Functor.OplaxMonoidal.δ F a b) ≫
      Functor.OplaxMonoidal.δ Q₂ (F.obj a) (F.obj b) ≫
      (γ.hom.app a ⊗ₘ γ.hom.app b) = γ.hom.app (a ⊗ b) ≫
      G.map (Functor.OplaxMonoidal.δ Q₁ a b) ≫ (d.app (Q₁.obj a)).app (Q₁.obj b)) :
    ∃ o : G.OplaxMonoidal,
      (∀ M N, @Functor.OplaxMonoidal.δ _ _ _ _ _ _ G o M N = (d.app M).app N) ∧
      @Functor.OplaxMonoidal.η _ _ _ _ _ _ G o =
        G.map (Functor.LaxMonoidal.ε Q₁) ≫ γ.inv.app (𝟙_ C₁) ≫
          Q₂.map (Functor.OplaxMonoidal.η F) ≫ inv (Functor.LaxMonoidal.ε Q₂) :=
  ⟨squareOplax Q₁ Q₂ F G γ d h, (fun _ _ ↦ rfl), rfl⟩

private theorem equivalenceStrongGeneric {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] (E : C ≌ D)
    (θ : Functor.uncurry.obj (curriedTensor C) ⋙ E.functor ≅
      (E.functor.prod E.functor) ⋙
        ((E.inverse.prod E.inverse) ⋙ Functor.uncurry.obj (curriedTensor C) ⋙ E.functor)) :
    letI := Monoidal.transport E
    ∀ (o : E.functor.OplaxMonoidal),
      @Functor.OplaxMonoidal.η _ _ _ _ _ _ E.functor o = 𝟙 _ →
      (∀ M N, @Functor.OplaxMonoidal.δ _ _ _ _ _ _ E.functor o M N =
        θ.hom.app (M, N)) →
      ∃ m : E.functor.Monoidal,
        (∀ M N, @Functor.OplaxMonoidal.δ _ _ _ _ _ _ E.functor
          m.toOplaxMonoidal M N = θ.hom.app (M, N)) ∧
        @Functor.OplaxMonoidal.η _ _ _ _ _ _ E.functor m.toOplaxMonoidal = 𝟙 _ := by
  letI := Monoidal.transport E
  intro o hη hδ
  letI : E.functor.OplaxMonoidal := o
  have hu : Functor.OplaxMonoidal.η E.functor = 𝟙 _ := hη
  have hd (M N) : Functor.OplaxMonoidal.δ E.functor M N =
      θ.hom.app (M, N) := hδ M N
  have : IsIso (Functor.OplaxMonoidal.η E.functor) := by
    rw [hu]
    infer_instance
  have : ∀ M N, IsIso (Functor.OplaxMonoidal.δ E.functor M N) := fun M N ↦ by
    rw [hd]
    infer_instance
  obtain ⟨m, hm, hu⟩ := strongOfOplax E.functor
  exact ⟨m, (fun M N ↦ (hm M N).trans (hd M N)), hu.trans hη⟩

private theorem oplax_constraints {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D] (F : C ⥤ D) [F.OplaxMonoidal] :
    (∀ M N P, F.map (α_ M N P).hom ≫ Functor.OplaxMonoidal.δ F M (N ⊗ P) ≫
      (𝟙 _ ⊗ₘ Functor.OplaxMonoidal.δ F N P) =
      Functor.OplaxMonoidal.δ F (M ⊗ N) P ≫
      (Functor.OplaxMonoidal.δ F M N ⊗ₘ 𝟙 _) ≫
      (α_ (F.obj M) (F.obj N) (F.obj P)).hom) ∧
    (∀ M, Functor.OplaxMonoidal.δ F (𝟙_ C) M ≫
      (Functor.OplaxMonoidal.η F ⊗ₘ 𝟙 _) ≫ (λ_ (F.obj M)).hom = F.map (λ_ M).hom) ∧
    (∀ M, Functor.OplaxMonoidal.δ F M (𝟙_ C) ≫
      (𝟙 _ ⊗ₘ Functor.OplaxMonoidal.η F) ≫ (ρ_ (F.obj M)).hom = F.map (ρ_ M).hom) := by
  refine ⟨?_, ?_, ?_⟩
  · intro M N P
    simpa only [id_tensorHom, tensorHom_id] using
      (Functor.OplaxMonoidal.associativity F M N P).symm
  · intro M
    simpa only [tensorHom_id] using Functor.OplaxMonoidal.left_unitality_hom F M
  · intro M
    simpa only [id_tensorHom] using Functor.OplaxMonoidal.right_unitality_hom F M

private theorem transported_unit_simplify {C₁ C₂ D₁ D₂ : Type*}
    [Category C₁] [Category C₂] [Category D₁] [Category D₂]
    [MonoidalCategory C₁] [MonoidalCategory C₂]
    (e₁ : C₁ ≌ D₁) (e₂ : C₂ ≌ D₂) :
    letI := Monoidal.transport e₁
    letI := Monoidal.transport e₂
    ∀ (m₁ : e₁.functor.Monoidal) (m₂ : e₂.functor.Monoidal)
      (F : C₁ ⥤ C₂) (G : D₁ ⥤ D₂) (γ : F ⋙ e₂.functor ≅ e₁.functor ⋙ G)
      (η : F.obj (𝟙_ C₁) ⟶ 𝟙_ C₂),
      @Functor.OplaxMonoidal.η _ _ _ _ _ _ e₁.functor m₁.toOplaxMonoidal = 𝟙 _ →
      @Functor.OplaxMonoidal.η _ _ _ _ _ _ e₂.functor m₂.toOplaxMonoidal = 𝟙 _ →
      G.map (@Functor.LaxMonoidal.ε _ _ _ _ _ _ e₁.functor m₁.toLaxMonoidal) ≫
        γ.inv.app (𝟙_ C₁) ≫ e₂.functor.map η ≫
          inv (@Functor.LaxMonoidal.ε _ _ _ _ _ _ e₂.functor m₂.toLaxMonoidal) =
        γ.inv.app (𝟙_ C₁) ≫ e₂.functor.map η := by
  letI := Monoidal.transport e₁
  letI := Monoidal.transport e₂
  intro m₁ m₂ F G γ η h₁ h₂
  letI : e₁.functor.Monoidal := m₁
  letI : e₂.functor.Monoidal := m₂
  have hε₁ : Functor.LaxMonoidal.ε e₁.functor = 𝟙 _ := by
    have h := Functor.Monoidal.ε_η e₁.functor
    erw [h₁, Category.comp_id] at h
    exact h
  rw [Functor.Monoidal.inv_ε]
  erw [hε₁, h₂, CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]

private theorem pullbackConstraintsGeneric
    {C₁ C₂ D₁ D₂ : Type*} [Category C₁] [Category C₂] [Category D₁] [Category D₂]
    [MonoidalCategory C₁] [MonoidalCategory C₂]
    (eY : C₁ ≌ D₁) (eX : C₂ ≌ D₂)
    (F : C₁ ⥤ C₂) (L : D₁ ⥤ D₂) (γ : F ⋙ eX.functor ≅ eY.functor ⋙ L)
    (θY : Functor.uncurry.obj (curriedTensor C₁) ⋙ eY.functor ≅
      (eY.functor.prod eY.functor) ⋙
        ((eY.inverse.prod eY.inverse) ⋙ Functor.uncurry.obj (curriedTensor C₁) ⋙ eY.functor))
    (θX : Functor.uncurry.obj (curriedTensor C₂) ⋙ eX.functor ≅
      (eX.functor.prod eX.functor) ⋙
        ((eX.inverse.prod eX.inverse) ⋙ Functor.uncurry.obj (curriedTensor C₂) ⋙ eX.functor)) :
    letI := Monoidal.transport eY
    letI := Monoidal.transport eX
    let TY := (eY.inverse.prod eY.inverse) ⋙ Functor.uncurry.obj (curriedTensor C₁) ⋙ eY.functor
    let TX := (eX.inverse.prod eX.inverse) ⋙ Functor.uncurry.obj (curriedTensor C₂) ⋙ eX.functor
    ∀ (oY : eY.functor.OplaxMonoidal) (oX : eX.functor.OplaxMonoidal)
      (hηY : @Functor.OplaxMonoidal.η _ _ _ _ _ _ eY.functor oY = 𝟙 _)
      (hηX : @Functor.OplaxMonoidal.η _ _ _ _ _ _ eX.functor oX = 𝟙 _)
      (hδY : ∀ M N, @Functor.OplaxMonoidal.δ _ _ _ _ _ _ eY.functor oY M N =
        θY.hom.app (M, N))
      (hδX : ∀ M N, @Functor.OplaxMonoidal.δ _ _ _ _ _ _ eX.functor oX M N =
        θX.hom.app (M, N))
      (d : TY ⋙ L ≅ (L.prod L) ⋙ TX)
      (δF : (Functor.postcompose₂.obj F).obj (curriedTensor C₁) ⟶
        (((Functor.whiskeringLeft₂ C₂).obj F).obj F).obj (curriedTensor C₂))
      (ηF : F.obj (𝟙_ C₁) ⟶ 𝟙_ C₂)
      (ηL : L.obj (eY.functor.obj (𝟙_ C₁)) ⟶ eX.functor.obj (𝟙_ C₂))
      (hi : ∃ o : F.OplaxMonoidal,
        (∀ M N, @Functor.OplaxMonoidal.δ _ _ _ _ _ _ F o M N = (δF.app M).app N) ∧
          @Functor.OplaxMonoidal.η _ _ _ _ _ _ F o = ηF)
      (hsquare : ∀ M N, eX.functor.map ((δF.app M).app N) ≫
        θX.hom.app (F.obj M, F.obj N) ≫
        TX.map (Prod.mkHom (γ.hom.app M) (γ.hom.app N)) =
          γ.hom.app (M ⊗ N) ≫ L.map (θY.hom.app (M, N)) ≫
            d.hom.app (eY.functor.obj M, eY.functor.obj N))
      (hunit : eX.functor.map ηF = γ.hom.app (𝟙_ C₁) ≫ ηL),
      TensorConstraintCondition L TY TX
        (eY.functor.obj (𝟙_ C₁)) (eX.functor.obj (𝟙_ C₂))
        (@MonoidalCategoryStruct.associator _ _ (Monoidal.transportStruct eY))
        (@MonoidalCategoryStruct.leftUnitor _ _ (Monoidal.transportStruct eY))
        (@MonoidalCategoryStruct.rightUnitor _ _ (Monoidal.transportStruct eY))
        (@MonoidalCategoryStruct.associator _ _ (Monoidal.transportStruct eX))
        (@MonoidalCategoryStruct.leftUnitor _ _ (Monoidal.transportStruct eX))
        (@MonoidalCategoryStruct.rightUnitor _ _ (Monoidal.transportStruct eX)) d.hom ηL := by
  letI := Monoidal.transport eY
  letI := Monoidal.transport eX
  dsimp only
  intro oY oX hηY hηX hδY hδX d δF ηF ηL hi hsquare hunit
  obtain ⟨mX, hδX, hηX⟩ := equivalenceStrongGeneric eX θX oX hηX hδX
  obtain ⟨mY, hδY, hηY⟩ := equivalenceStrongGeneric eY θY oY hηY hδY
  letI : eX.functor.Monoidal := mX
  letI : eY.functor.Monoidal := mY
  letI : eX.functor.OplaxMonoidal := mX.toOplaxMonoidal
  letI : eY.functor.OplaxMonoidal := mY.toOplaxMonoidal
  obtain ⟨oF, hδF, hηF⟩ := hi
  letI : F.OplaxMonoidal := oF
  let dn := (Functor.isoWhiskerRight (nativeTensorIso eY).symm
      L) ≪≫ d ≪≫
    Functor.isoWhiskerLeft (L.prod L)
      (nativeTensorIso eX)
  let δ := curryComparison L dn.hom
  have hδ (M N : D₁) : (δ.app M).app N =
      d.hom.app (M, N) := by
    dsimp only [δ, curryComparison, dn, Iso.trans_hom, NatTrans.comp_app,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, Iso.symm_hom,
      nativeTensorIso, NatIso.ofComponents_hom_app, NatIso.ofComponents_inv_app,
      Iso.refl_hom, Iso.refl_inv]
    erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  have hsq : ∀ a b, eX.functor.map
      (Functor.OplaxMonoidal.δ F a b) ≫
      Functor.OplaxMonoidal.δ eX.functor
        (F.obj a) (F.obj b) ≫
      (γ.hom.app a ⊗ₘ γ.hom.app b) =
      γ.hom.app (a ⊗ b) ≫
      L.map (Functor.OplaxMonoidal.δ eY.functor a b) ≫
      (δ.app (eY.functor.obj a)).app (eY.functor.obj b) := by
    intro a b
    rw [hδF, hδX, hδY, hδ]
    convert! hsquare a b using 1
    all_goals rw [transportedTensor_map]
  obtain ⟨oL, hδL, hηL⟩ := squareOplaxData eY.functor eX.functor
    F L γ δ hsq
  letI : L.OplaxMonoidal := oL
  have hη : Functor.OplaxMonoidal.η L =
      ηL := by
    erw [hηL, transported_unit_simplify eY
      eX mY mX _ _ _ _ hηY hηX, hηF]
    have hu : eX.functor.map ηF =
      γ.hom.app (𝟙_ _) ≫ ηL :=
      hunit
    erw [hu, Iso.inv_hom_id_app_assoc]
  have hd (M N) : Functor.OplaxMonoidal.δ L M N =
      d.hom.app (M, N) := (hδL M N).trans (hδ M N)
  have h := oplax_constraints L
  simp only [hd, hη] at h
  dsimp only [TensorConstraintCondition]
  convert! h using 1 <;>
    simp only [transportedTensor_map]
  all_goals rfl

private theorem pullback_constraints {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hi : ∃ o : (internalDerivedPullback Λ f).OplaxMonoidal,
      (∀ M N, @Functor.OplaxMonoidal.δ _ _ _ _ _ _ (internalDerivedPullback Λ f) o M N =
        ((internalDelta Λ f).app M).app N) ∧
      @Functor.OplaxMonoidal.η _ _ _ _ _ _ (internalDerivedPullback Λ f) o =
        (normalizationDerivedInternalUnit Λ f).hom)
    (hsquare : ∀ M N : DerivedCategory (internalModules Λ Y),
      (derivedEquivalence Λ X).functor.map (((internalDelta Λ f).app M).app N) ≫
        (tensorComparison Λ X).hom.app
          ((internalDerivedPullback Λ f).obj M, (internalDerivedPullback Λ f).obj N) ≫
        (tensor Λ X).map (Prod.mkHom ((derivedPullComparison Λ f).hom.app M)
          ((derivedPullComparison Λ f).hom.app N)) =
      (derivedPullComparison Λ f).hom.app (M ⊗ N) ≫
        (derivedPullback Λ f).map ((tensorComparison Λ Y).hom.app (M, N)) ≫
        (tensorPullComparison Λ f).hom.app
          ((derivedEquivalence Λ Y).functor.obj M, (derivedEquivalence Λ Y).functor.obj N))
    (hunit : (derivedEquivalence Λ X).functor.map (normalizationDerivedInternalUnit Λ f).hom =
      (derivedPullComparison Λ f).hom.app (𝟙_ _) ≫ normalizationDerivedSectionUnit Λ f) :
    TensorConstraintCondition (derivedPullback Λ f) (tensor Λ Y) (tensor Λ X)
      (tensorUnit Λ Y) (tensorUnit Λ X)
      (normalizationDerivedAssociator Λ Y) (normalizationDerivedLeftUnitor Λ Y)
      (normalizationDerivedRightUnitor Λ Y)
      (normalizationDerivedAssociator Λ X) (normalizationDerivedLeftUnitor Λ X)
      (normalizationDerivedRightUnitor Λ X)
      (tensorPullComparison Λ f).hom (normalizationDerivedSectionUnit Λ f) := by
  obtain ⟨_, _, oX, hηX, hδX⟩ :=
    (KFlatSectionComparison.section_kflat_tensor_comparison.{u, u + 2, u + 1} Λ X).2.2.2.2.2.2.2.2
  obtain ⟨_, _, oY, hηY, hδY⟩ :=
    (KFlatSectionComparison.section_kflat_tensor_comparison.{u, u + 2, u + 1} Λ Y).2.2.2.2.2.2.2.2
  exact pullbackConstraintsGeneric (derivedEquivalence Λ Y) (derivedEquivalence Λ X)
    (internalDerivedPullback Λ f) (derivedPullback Λ f) (derivedPullComparison Λ f)
    (tensorComparison Λ Y) (tensorComparison Λ X) oY oX hηY hηX hδY hδX
    (tensorPullComparison Λ f) (internalDelta Λ f) (normalizationDerivedInternalUnit Λ f).hom
    (normalizationDerivedSectionUnit Λ f) hi hsquare hunit

private theorem equivalenceConstraintsGeneric {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] (E : C ≌ D)
    (θ : Functor.uncurry.obj (curriedTensor C) ⋙ E.functor ≅
      (E.functor.prod E.functor) ⋙
        ((E.inverse.prod E.inverse) ⋙ Functor.uncurry.obj (curriedTensor C) ⋙ E.functor))
    (o : @Functor.OplaxMonoidal C _ _ D _ (Monoidal.transport E) E.functor)
    (hη : @Functor.OplaxMonoidal.η _ _ _ _ _ (Monoidal.transport E) E.functor o = 𝟙 _)
    (hδ : ∀ M N, @Functor.OplaxMonoidal.δ _ _ _ _ _ (Monoidal.transport E)
      E.functor o M N = θ.hom.app (M, N)) :
    TensorConstraintCondition E.functor (Functor.uncurry.obj (curriedTensor C))
      ((E.inverse.prod E.inverse) ⋙ Functor.uncurry.obj (curriedTensor C) ⋙ E.functor)
      (𝟙_ C) (E.functor.obj (𝟙_ C)) (fun M N P ↦ α_ M N P)
      (fun M ↦ λ_ M) (fun M ↦ ρ_ M)
      (@MonoidalCategoryStruct.associator _ _ (Monoidal.transportStruct E))
      (@MonoidalCategoryStruct.leftUnitor _ _ (Monoidal.transportStruct E))
      (@MonoidalCategoryStruct.rightUnitor _ _ (Monoidal.transportStruct E)) θ.hom (𝟙 _) := by
  let _ : MonoidalCategory D :=
    Monoidal.transport E
  letI : E.functor.OplaxMonoidal := o
  have hd (M N) : Functor.OplaxMonoidal.δ E.functor M N =
      θ.hom.app (M, N) := hδ M N
  have hu : Functor.OplaxMonoidal.η E.functor = 𝟙 _ := hη
  have h := oplax_constraints E.functor
  simp only [hd, hu] at h
  dsimp only [TensorConstraintCondition]
  simp only [transportedTensor_map, Functor.prod_obj]
  convert! h using 1

private theorem equivalence_constraints (T : Scheme.{u}) :
    TensorConstraintCondition
      (derivedFunctor Λ T) (Functor.uncurry.obj (CondensedRing.derivedTensor Λ T))
      (tensor Λ T) (𝟙_ (DerivedCategory (internalModules Λ T))) (tensorUnit Λ T)
      (fun M N P ↦ α_ M N P) (fun M ↦ λ_ M) (fun M ↦ ρ_ M)
      (normalizationDerivedAssociator Λ T) (normalizationDerivedLeftUnitor Λ T)
      (normalizationDerivedRightUnitor Λ T) (tensorComparison Λ T).hom (𝟙 _) := by
  obtain ⟨e, he, o, hη, hδ⟩ :=
    (KFlatSectionComparison.section_kflat_tensor_comparison.{u, u + 2, u + 1} Λ T).2.2.2.2.2.2.2.2
  exact equivalenceConstraintsGeneric (derivedEquivalence Λ T) (tensorComparison Λ T) o hη hδ

/-- The derived section equivalence identifies the specified tensor and actual pullback maps.
Source: Stacks Project, Cohomology on Sites, Tag 07A4, lemma-pullback-tensor-product
(auxiliary; not a blueprint node).

Proof.
1. Use the chosen K-flat representative comparison for the tensor equation and
   the specified oplax structure on the section equivalence for its constraints.
2. Conjugate the actual internal tensor isomorphism by the fixed equivalence,
   tensor comparison, pullback comparison and counits. Site tensor descent makes
   restriction to flat-term K-flat representatives injective. The actual
   representative square identifies this conjugate with tensorPullComparison.
3. Cancel the equivalence comparisons to get the actual oplax square. Equality
   of the inverse natural isomorphisms gives the actual lax square.
4. Cancel the regular-unit comparisons in the actual representative unit equation.
   Functoriality identifies the remaining composite with the localized scalar unit.
5. The generic derived monoidal construction gives internalDelta its oplax laws.
   The proved comparison of the ordinary mate and canonical monoidal structures
   identifies its unit. Transport across the strong section equivalences and the
   fixed pullback comparison; the tensor and unit squares identify its fields.
   The transported oplax laws are the required final constraint equations.
-/
theorem section_derived_tensor_normalization {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (∀ T : Scheme.{u}, TensorRepresentativeCondition Λ T (qTensor Λ T)) ∧
    (∀ T : Scheme.{u}, TensorConstraintCondition
      (derivedFunctor Λ T) (Functor.uncurry.obj (CondensedRing.derivedTensor Λ T))
      (tensor Λ T) (𝟙_ (DerivedCategory (internalModules Λ T))) (tensorUnit Λ T)
      (fun M N P ↦ α_ M N P) (fun M ↦ λ_ M) (fun M ↦ ρ_ M)
      (normalizationDerivedAssociator Λ T) (normalizationDerivedLeftUnitor Λ T)
      (normalizationDerivedRightUnitor Λ T) (tensorComparison Λ T).hom
        (cast (by rfl) (𝟙 (tensorUnit Λ T)))) ∧
    (∀ M N : DerivedCategory (internalModules Λ Y),
      (derivedEquivalence Λ X).functor.map (((internalDelta Λ f).app M).app N) ≫
          (tensorComparison Λ X).hom.app
            ((internalDerivedPullback Λ f).obj M, (internalDerivedPullback Λ f).obj N) ≫
          (tensor Λ X).map (Prod.mkHom
            ((derivedPullComparison Λ f).hom.app M) ((derivedPullComparison Λ f).hom.app N)) =
        (derivedPullComparison Λ f).hom.app (M ⊗ N) ≫
          (derivedPullback Λ f).map ((tensorComparison Λ Y).hom.app (M, N)) ≫
          (tensorPullComparison Λ f).hom.app
            ((derivedEquivalence Λ Y).functor.obj M, (derivedEquivalence Λ Y).functor.obj N)) ∧
    (∀ M N : DerivedCategory (internalModules Λ Y),
      (tensor Λ X).map (Prod.mkHom
          ((derivedPullComparison Λ f).inv.app M) ((derivedPullComparison Λ f).inv.app N)) ≫
          (tensorComparison Λ X).inv.app
            ((internalDerivedPullback Λ f).obj M, (internalDerivedPullback Λ f).obj N) ≫
          (derivedEquivalence Λ X).functor.map
            (((normalizationDerivedInternalMu Λ f).app M).app N) =
        (tensorPullComparison Λ f).inv.app
            ((derivedEquivalence Λ Y).functor.obj M, (derivedEquivalence Λ Y).functor.obj N) ≫
          (derivedPullback Λ f).map ((tensorComparison Λ Y).inv.app (M, N)) ≫
          (derivedPullComparison Λ f).inv.app (M ⊗ N)) ∧
    ((derivedEquivalence Λ X).functor.map
        (normalizationDerivedInternalUnit Λ f).hom =
      (derivedPullComparison Λ f).hom.app (𝟙_ (DerivedCategory (internalModules Λ Y))) ≫
        cast (by rfl) (normalizationDerivedSectionUnit Λ f)) ∧
    TensorConstraintCondition (derivedPullback Λ f) (tensor Λ Y) (tensor Λ X)
      (tensorUnit Λ Y) (tensorUnit Λ X)
      (normalizationDerivedAssociator Λ Y) (normalizationDerivedLeftUnitor Λ Y)
      (normalizationDerivedRightUnitor Λ Y)
      (normalizationDerivedAssociator Λ X) (normalizationDerivedLeftUnitor Λ X)
      (normalizationDerivedRightUnitor Λ X)
      (tensorPullComparison Λ f).hom (normalizationDerivedSectionUnit Λ f) := by
  have hsq := square_eq Λ f (actualComparisonIso_eq Λ f)
  have hf := genericSquare_hom (Functor.uncurry.obj (CondensedRing.derivedTensor Λ Y))
    (Functor.uncurry.obj (CondensedRing.derivedTensor Λ X))
    (derivedEquivalence Λ Y) (derivedEquivalence Λ X).functor
    (internalDerivedPullback Λ f) (derivedPullback Λ f) (tensor Λ Y) (tensor Λ X)
    (tensorComparison Λ Y) (tensorComparison Λ X) (derivedPullComparison Λ f)
    (internalTensorIso Λ f) (tensorPullComparison Λ f)
    (by simpa only [squareLeft, squareRight] using hsq)
  simp only [internalTensorIso_hom] at hf
  refine ⟨?_, equivalence_constraints Λ, hf, ?_, unit_normalization Λ f,
    pullback_constraints Λ f (internal_oplax_compatible Λ f) hf (unit_normalization Λ f)⟩
  · intro T
    unfold qTensor
    exact (tensor_representatives Λ T).exists.choose_spec
  · intro M N
    have h := genericSquare_inv (Functor.uncurry.obj (CondensedRing.derivedTensor Λ Y))
      (Functor.uncurry.obj (CondensedRing.derivedTensor Λ X))
      (derivedEquivalence Λ Y) (derivedEquivalence Λ X).functor
      (internalDerivedPullback Λ f) (derivedPullback Λ f) (tensor Λ Y) (tensor Λ X)
      (tensorComparison Λ Y) (tensorComparison Λ X) (derivedPullComparison Λ f)
      (internalTensorIso Λ f) (tensorPullComparison Λ f)
      (by simpa only [squareLeft, squareRight] using hsq) M N
    rw [internalTensorIso_inv] at h
    exact h

end AlgebraicGeometry.ProEtale.ModuleRingedComparison
