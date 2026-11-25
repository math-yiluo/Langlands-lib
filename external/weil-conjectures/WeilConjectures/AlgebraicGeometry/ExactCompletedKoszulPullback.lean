/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ExtensionTensorComparison
public import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatAllIndependentCoefficients
public import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.FlatScalarRestrictionKFlat
public import WeilConjectures.Algebra.Homology.KFlatFixedTensorTriangulated
public import WeilConjectures.Algebra.Homology.KFlatResolution
public import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
public import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import WeilConjectures.AlgebraicGeometry.CoefficientRingedSequenceSite
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionCompletedFinitePull
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionInverseImageExists
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionKoszulReflector
public import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
public import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.CategoryTheory.FlatScalarKoszulTowerComparison
public import WeilConjectures.CategoryTheory.NatTransFromResolvingClass
public import WeilConjectures.CategoryTheory.RingedToposKFlatPullback
public import WeilConjectures.SecSmoothPurity.CochainTensorCoherenceData
import all WeilConjectures.CategoryTheory.FlatScalarKoszulTowerComparison
import all WeilConjectures.AlgebraicGeometry.CompletedPullbackAdjunction
import all WeilConjectures.AlgebraicGeometry.ExactProductFunctorRoosResolution
import WeilConjectures.AlgebraicGeometry.ExactProductFunctorStrictLimit
import WeilConjectures.AlgebraicGeometry.StrictCompletedKoszulTowerPullback
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic

/-! # Koszul units under exact inverse image preserving products

Source: Stacks Project, algebraization.tex, Tag 0A0E; sites-cohomology.tex, Tags
07A4 and 0941 (auxiliary; not a blueprint node).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section
-- Keep the chosen localizations and completed coefficient limits from unfolding in proof search.
attribute [local irreducible] HasDerivedCategory.standard ConstantCompletion.completed
  ConstantCompletion.derivedPull
universe u w a b c d wA wB

namespace CategoryTheory
set_option backward.defeqAttrib.useBackward true
-- Cache the pointwise complex limit instances instead of rebuilding them at every projection.
private theorem complexTowerLimits (T : Type a) [Category.{c} T] [Abelian T]
    [HasLimitsOfShape ℕᵒᵖ T] : HasLimitsOfShape ℕᵒᵖ (CochainComplex T ℤ) := by
  infer_instance

private theorem complexNatProductLimits (T : Type a) [Category.{c} T] [Abelian T]
    [HasCountableProducts T] : HasLimitsOfShape (Discrete ℕ) (CochainComplex T ℤ) := by
  infer_instance

private theorem complexTowerLimit (T : Type a) [Category.{c} T] [Abelian T]
    [HasLimitsOfShape ℕᵒᵖ T] (X : ℕᵒᵖ ⥤ CochainComplex T ℤ) : HasLimit X := by
  let := complexTowerLimits T
  exact HasLimitsOfShape.has_limit X

private theorem complexCountableProduct (T : Type a) [Category.{c} T] [Abelian T]
    [HasCountableProducts T] (X : Discrete ℕ ⥤ CochainComplex T ℤ) : HasLimit X := by
  let := complexNatProductLimits T
  exact HasLimitsOfShape.has_limit X

attribute [local instance] complexTowerLimits complexNatProductLimits
  complexTowerLimit complexCountableProduct

variable {A : Type a} {B : Type b} [Category.{c} A] [Category.{d} B]
  [Abelian A] [Abelian B] [HasCountableProducts A] [HasCountableProducts B]
  [HasLimitsOfShape ℕᵒᵖ A] [HasLimitsOfShape ℕᵒᵖ B]
  [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wA} (ℕᵒᵖ ⥤ A)]
  [HasDerivedCategory.{wB} B] [HasDerivedCategory.{wB} (ℕᵒᵖ ⥤ B)]
  [IsGrothendieckAbelian.{c} (ℕᵒᵖ ⥤ A)]
  [IsGrothendieckAbelian.{d} (ℕᵒᵖ ⥤ B)]

-- Extend the normalized Roos inclusion identity to all complexes.
private theorem normalizedLimit
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ _ _).obj F)]
    [PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ _ _).obj F)]
    (LA : DerivedCategory.{wA} (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory.{wA} A)
    (LB : DerivedCategory.{wB} (ℕᵒᵖ ⥤ B) ⥤ DerivedCategory.{wB} B)
    (etaA : HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
      (lim : (ℕᵒᵖ ⥤ CochainComplex A ℤ) ⥤ CochainComplex A ℤ) ⋙
        DerivedCategory.Q.{wA} ⟶ DerivedCategory.Q.{wA} ⋙ LA)
    (etaB : HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
      (lim : (ℕᵒᵖ ⥤ CochainComplex B ℤ) ⥤ CochainComplex B ℤ) ⋙
        DerivedCategory.Q.{wB} ⟶ DerivedCategory.Q.{wB} ⋙ LB)
    (h : StrictLimitAssertions F LA LB etaA etaB) :
    ∃ (beta : ∀ X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
        (F.mapHomologicalComplex (.up ℤ)).obj (limit X.asFunctor) ≅
          limit ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex
            (.up ℤ)).obj X).asFunctor)
      (alpha : LA ⋙ F.mapDerivedCategory ≅
        ((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapDerivedCategory ⋙ LB),
      (∀ X n, (beta X).hom ≫ limit.π _ (op n) =
        (F.mapHomologicalComplex (.up ℤ)).map (limit.π X.asFunctor (op n))) ∧
      ∀ X, F.mapDerivedCategory.map (etaA.app X) ≫
          alpha.hom.app (DerivedCategory.Q.obj X) ≫
          LB.map (((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapDerivedCategoryFactors.hom.app X) =
        F.mapDerivedCategoryFactors.hom.app (limit X.asFunctor) ≫
          DerivedCategory.Q.map (beta X).hom ≫
          etaB.app ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex
            (.up ℤ)).obj X) := by
  classical
  rcases h with ⟨HA, HB, hAobj, hBobj, chiA, chiB, thetaA, thetaB, psi, kappa, beta,
    lambda, laws⟩
  have hcoord := And.intro laws.1 laws.2.1
  have hAm := @laws.2.2.1
  have hBm := @laws.2.2.2.1
  have hAn := @laws.2.2.2.2.1
  have hBn := @laws.2.2.2.2.2.1
  have hkappa := laws.2.2.2.2.2.2.2.1
  have hsquare := laws.2.2.2.2.2.2.2.2.1
  have hbeta := laws.2.2.2.2.2.2.2.2.2.1
  let Fc := F.mapHomologicalComplex (ComplexShape.up ℤ)
  let Ftw := (Functor.whiskeringRight ℕᵒᵖ _ _).obj F
  let Ft := Ftw.mapHomologicalComplex (ComplexShape.up ℤ)
  let FD := F.mapDerivedCategory
  have hcA X p : (chiA X p).hom =
      (eqToIso (congrArg (fun V ↦ V.X (p + 1)) (hAobj X))).hom ≫
        (signedχ X p).hom := by
    simpa [signedχ, roosχ, Category.assoc] using hcoord.1 X p
  have hcB X p : (chiB X p).hom =
      (eqToIso (congrArg (fun V ↦ V.X (p + 1)) (hBobj X))).hom ≫
        (signedχ X p).hom := by
    simpa [signedχ, roosχ, Category.assoc] using hcoord.2 X p
  choose ιA hiA using fun X ↦ inclusion_exists X (HA.obj X) (hAobj X) (chiA X) (hcA X)
  choose ιB hiB using fun X ↦ inclusion_exists X (HB.obj X) (hBobj X) (chiB X) (hcB X)
  have hnA {X Y : CochainComplex (ℕᵒᵖ ⥤ A) ℤ} (f : X ⟶ Y) :
      roosLimitFunctor.map f ≫ ιA Y = ιA X ≫ HA.map f :=
    inclusion_natural HA chiA hAm ιA hiA f
  have hnB {X Y : CochainComplex (ℕᵒᵖ ⥤ B) ℤ} (f : X ⟶ Y) :
      roosLimitFunctor.map f ≫ ιB Y = ιB X ≫ HB.map f :=
    inclusion_natural HB chiB hBm ιB hiB f
  have huA : ∀ X, etaA.app X ≫ thetaA.hom.app X = DerivedCategory.Q.map (ιA X) := by
    apply normalized_unit HA LA etaA thetaA ιA hnA
    intro I hI hinj
    obtain ⟨ι, _, hc, hu⟩ := hAn I hinj
    have he : ι = ιA I := inclusion_unique (chiA I) ι (ιA I) hc (hiA I)
    simpa only [he] using hu
  have huB : ∀ X, etaB.app X ≫ thetaB.hom.app X = DerivedCategory.Q.map (ιB X) := by
    apply normalized_unit HB LB etaB thetaB ιB hnB
    intro I hI hinj
    obtain ⟨ι, _, hc, hu⟩ := hBn I hinj
    have he : ι = ιB I := inclusion_unique (chiB I) ι (ιB I) hc (hiB I)
    simpa only [he] using hu
  have hι (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
      Fc.map (ιA I) ≫ (kappa I).hom = (beta I).hom ≫ ιB (Ft.obj I) := by
    apply HomologicalComplex.Hom.ext
    funext i
    obtain ⟨p, rfl⟩ : ∃ p : ℤ, i = p + 1 := ⟨i - 1, by omega⟩
    apply (cancel_mono (chiB (Ft.obj I) p).hom).mp
    apply biprod.hom_ext
    · apply product_component_ext _ (p + 1)
      intro n
      dsimp only [HomologicalComplex.comp_f, Fc, Functor.mapHomologicalComplex_map_f]
      simp only [Category.assoc]
      erw [(hkappa I p n).1]
      rw [← F.map_comp]
      simp only [← Category.assoc, hiA, hiB]
      simp only [Category.assoc, biprod.lift_fst_assoc]
      have hπA := congrArg (fun z ↦ z.f (p + 1))
        (Pi.lift_comp_π (fun n : ℕ ↦ limit.π I.asFunctor (op n)) n)
      have hπB := congrArg (fun z ↦ z.f (p + 1))
        (Pi.lift_comp_π (fun n : ℕ ↦ limit.π (Ft.obj I).asFunctor (op n)) n)
      simp only [HomologicalComplex.comp_f] at hπA hπB
      erw [hπA, hπB]
      exact (congrArg (fun z ↦ z.f (p + 1)) (hbeta I n)).symm
    · apply product_component_ext _ p
      intro n
      dsimp only [HomologicalComplex.comp_f, Fc, Functor.mapHomologicalComplex_map_f]
      simp only [Category.assoc]
      erw [(hkappa I p n).2]
      rw [← F.map_comp]
      simp only [← Category.assoc, hiA, hiB]
      simp [Category.assoc]
  have hunit (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
      FD.map (etaA.app I) ≫ lambda.hom.app (DerivedCategory.Q.obj I) ≫
        LB.map (Ftw.mapDerivedCategoryFactors.hom.app I) =
      F.mapDerivedCategoryFactors.hom.app (limit I.asFunctor) ≫
        DerivedCategory.Q.map (beta I).hom ≫ etaB.app (Ft.obj I) := by
    apply (cancel_mono (thetaB.hom.app (Ft.obj I))).mp
    calc
      _ = FD.map (etaA.app I ≫ thetaA.hom.app I) ≫
          F.mapDerivedCategoryFactors.hom.app (HA.obj I) ≫
          DerivedCategory.Q.map (kappa I).hom := by
        rw [Functor.map_comp]
        simpa only [Category.assoc] using congrArg (fun z ↦ FD.map (etaA.app I) ≫ z)
          (hsquare I).symm
      _ = F.mapDerivedCategoryFactors.hom.app (limit I.asFunctor) ≫
          DerivedCategory.Q.map (Fc.map (ιA I) ≫ (kappa I).hom) := by
        rw [huA, F.mapDerivedCategoryFactors_hom_naturality_assoc]
        rw [Functor.map_comp]
      _ = _ := by rw [hι, Functor.map_comp]; simp only [Category.assoc, huB]
  exact ⟨beta, lambda, hbeta, hunit⟩

omit [HasCountableProducts A] [HasDerivedCategory A]
  [HasDerivedCategory (ℕᵒᵖ ⥤ A)] [IsGrothendieckAbelian.{c} (ℕᵒᵖ ⥤ A)] in
private theorem ordinaryLimitIso_hom_π
    (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (n : ℤ) (m : ℕᵒᵖ) :
    ((ordinaryLimitIso (A := A)).hom.app X).f n ≫
        (limit.π X.asFunctor m).f n = limit.π (X.X n) m := by
  exact HomologicalComplex.limitXIso_hom_π_f X.asFunctor n m

omit [HasCountableProducts A] [HasDerivedCategory A]
  [HasDerivedCategory (ℕᵒᵖ ⥤ A)] [IsGrothendieckAbelian.{c} (ℕᵒᵖ ⥤ A)] in
private theorem ordinaryLimitIso_inv_π
    (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (n : ℤ) (m : ℕᵒᵖ) :
    ((ordinaryLimitIso (A := A)).inv.app X).f n ≫ limit.π (X.X n) m =
        (limit.π X.asFunctor m).f n := by
  rw [← ordinaryLimitIso_hom_π X n m, ← Category.assoc]
  have hi := congrArg (fun f ↦ f.f n) ((ordinaryLimitIso (A := A)).inv_hom_id_app X)
  simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f] at hi
  rw [hi, Category.id_comp]

-- Reconcile limits of complexes with degreewise limits.
private theorem normalizedActualLimit
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ _ _).obj F)]
    [PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ _ _).obj F)]
    (LA : DerivedCategory.{wA} (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory.{wA} A)
    (LB : DerivedCategory.{wB} (ℕᵒᵖ ⥤ B) ⥤ DerivedCategory.{wB} B)
    (etaA : (lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q.{wA} ⟶ DerivedCategory.Q.{wA} ⋙ LA)
    (etaB : (lim : (ℕᵒᵖ ⥤ B) ⥤ B).mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q.{wB} ⟶ DerivedCategory.Q.{wB} ⋙ LB)
    (h : StrictLimitAssertions F LA LB
      (Functor.whiskerRight (ordinaryLimitIso (A := A)).inv DerivedCategory.Q ≫ etaA)
      (Functor.whiskerRight (ordinaryLimitIso (A := B)).inv DerivedCategory.Q ≫ etaB)) :
    ∃ (beta : ∀ X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
        (F.mapHomologicalComplex (.up ℤ)).obj
          (((lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (.up ℤ)).obj X) ≅
        ((lim : (ℕᵒᵖ ⥤ B) ⥤ B).mapHomologicalComplex (.up ℤ)).obj
          ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex (.up ℤ)).obj X))
      (alpha : LA ⋙ F.mapDerivedCategory ≅
        ((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapDerivedCategory ⋙ LB),
      (∀ X n m, ((beta X).hom.f n) ≫ limit.π _ m = F.map (limit.π (X.X n) m)) ∧
      ∀ X, F.mapDerivedCategory.map (etaA.app X) ≫
          alpha.hom.app (DerivedCategory.Q.obj X) =
        F.mapDerivedCategoryFactors.hom.app _ ≫ DerivedCategory.Q.map (beta X).hom ≫
          etaB.app ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex
            (.up ℤ)).obj X) ≫
          LB.map (((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapDerivedCategoryFactors.inv.app X)
        := by
  obtain ⟨beta, alpha, hb, ha⟩ := normalizedLimit F LA LB _ _ h
  let Fc := F.mapHomologicalComplex (.up ℤ)
  let Ft := ((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex (.up ℤ)
  let b := fun X ↦ Fc.mapIso ((ordinaryLimitIso (A := A)).app X) ≪≫ beta X ≪≫
    ((ordinaryLimitIso (A := B)).app (Ft.obj X)).symm
  refine ⟨b, alpha, ?_, ?_⟩
  · intro X n m
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, m = op k := ⟨m.unop, rfl⟩
    dsimp only [b, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
      HomologicalComplex.comp_f, Fc, Functor.mapHomologicalComplex_map_f]
    simp only [Category.assoc]
    erw [ordinaryLimitIso_inv_π (Ft.obj X) n (op k)]
    erw [← HomologicalComplex.comp_f, hb]
    dsimp only [Functor.mapHomologicalComplex_map_f]
    erw [← F.map_comp, ordinaryLimitIso_hom_π]
  · intro X
    apply (cancel_epi (F.mapDerivedCategory.map
      (DerivedCategory.Q.map ((ordinaryLimitIso (A := A)).inv.app X)))).mp
    apply (cancel_mono
      (LB.map (((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapDerivedCategoryFactors.hom.app X))).mp
    have he := ha X
    dsimp only [NatTrans.comp_app, Functor.whiskerRight_app] at he
    simp only [Functor.map_comp, Category.assoc] at he
    simp only [Category.assoc]
    rw [he]
    dsimp only [b, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
    simp only [Functor.map_comp, Category.assoc]
    rw [F.mapDerivedCategoryFactors_hom_naturality_assoc]
    dsimp only [Fc, Ft]
    simp only [← DerivedCategory.Q.map_comp_assoc,
      ← (F.mapHomologicalComplex (.up ℤ)).map_comp_assoc, Iso.app_hom, Iso.app_inv,
      Iso.inv_hom_id_app, Functor.map_id, Category.id_comp]
    simp only [← LB.map_comp, Iso.inv_hom_id_app]
    erw [LB.map_id, Category.comp_id]
    rfl

end CategoryTheory

namespace CategoryTheory.ConstantCompletion
set_option synthInstance.maxSize 2048
set_option backward.defeqAttrib.useBackward true

variable {C D : Type v} [SmallCategory C] [SmallCategory D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {L : Sheaf J (Type v) ⥤ Sheaf K (Type v)}
  (F : InverseImageData L) (V : Sheaf K (Type v) ⥤ Sheaf J (Type v)) (adj : L ⊣ V)
  [PreservesFiniteLimits L]
  {R : Sheaf J CommRingCat.{v}} {S : Sheaf K CommRingCat.{v}}
  (c : F.rings.obj R ⟶ S) [IsIso c]

include V adj in
private theorem pull_exact :
    PreservesFiniteLimits (pull F c) ∧ PreservesFiniteColimits (pull F c) := by
  refine ⟨pull_finiteLimits_of_isIso F c, ?_⟩
  obtain ⟨G, _, aM, _⟩ := module_adjunction_exists V adj F c
  have := aM.leftAdjoint_preservesColimits
  infer_instance

private theorem underlying_products (O : Sheaf J CommRingCat.{v}) :
    PreservesLimitsOfShape (Discrete ℕ) (underlying O) := by
  let U := sheafCompose J (CategoryTheory.forget AddCommGrpCat.{v})
  have : PreservesLimitsOfShape (Discrete ℕ) (U ⋙ sheafToPresheaf J (Type v)) := by
    change PreservesLimitsOfShape (Discrete ℕ)
      (sheafToPresheaf J AddCommGrpCat.{v} ⋙
        (Functor.whiskeringRight _ _ _).obj (CategoryTheory.forget AddCommGrpCat.{v}))
    infer_instance
  have : PreservesLimitsOfShape (Discrete ℕ) U :=
    preservesLimitsOfShape_of_reflects_of_preserves U (sheafToPresheaf J (Type v))
  let B := siteModuleRings O
  have : PreservesLimitsOfShape (Discrete ℕ)
      (SheafOfModules.toSheaf B ⋙ sheafToPresheaf J AddCommGrpCat.{v}) := by
    change PreservesLimitsOfShape (Discrete ℕ)
      (SheafOfModules.forget B ⋙ PresheafOfModules.toPresheaf B.obj)
    infer_instance
  have : PreservesLimitsOfShape (Discrete ℕ) (SheafOfModules.toSheaf B) :=
    preservesLimitsOfShape_of_reflects_of_preserves _
      (sheafToPresheaf J AddCommGrpCat.{v})
  exact comp_preservesLimitsOfShape (SheafOfModules.toSheaf B) U

open SheafOfModules SheafOfModules.GeometricConstruction in
omit [PreservesFiniteLimits L] in
private theorem pull_products [PreservesLimitsOfShape (Discrete ℕ) L] :
    PreservesLimitsOfShape (Discrete ℕ) (pull F c) := by
  have : PreservesLimitsOfShape (Discrete ℕ) (underlying R) := underlying_products R
  have : PreservesLimitsOfShape (Discrete ℕ) (underlying (F.rings.obj R)) :=
    underlying_products (F.rings.obj R)
  have : PreservesLimitsOfShape (Discrete ℕ) (underlying R ⋙ L) := inferInstance
  have : PreservesLimitsOfShape (Discrete ℕ)
      ((F.algebra R).modules ⋙ underlying (F.rings.obj R)) :=
    preservesLimitsOfShape_of_natIso (F.algebra R).moduleUnderlying.symm
  have : ReflectsLimitsOfShape (Discrete ℕ) (underlying (F.rings.obj R)) :=
    reflectsLimitsOfShape_of_reflectsIsomorphisms
  have : PreservesLimitsOfShape (Discrete ℕ) (F.algebra R).modules :=
    preservesLimitsOfShape_of_reflects_of_preserves _ (underlying (F.rings.obj R))
  have : (restriction c).IsEquivalence := restrictScalars_equivalence
    ((sheafCompose K (forget₂ CommRingCat RingCat)).mapIso (asIso c))
  have := (tensorAdjunction c).isEquivalence_left_of_isEquivalence_right
  change PreservesLimitsOfShape (Discrete ℕ) ((F.algebra R).modules ⋙ tensorFunctor c)
  infer_instance

private noncomputable def pullDerivedIso :
    letI := HasDerivedCategory.standard (Mod R)
    letI := HasDerivedCategory.standard (Mod S)
    letI := (pull_exact F V adj c).1
    letI := (pull_exact F V adj c).2
    (derivedPull F V adj c).functor ≅ (pull F c).mapDerivedCategory := by
  letI := HasDerivedCategory.standard (Mod R)
  letI := HasDerivedCategory.standard (Mod S)
  have := (pull_exact F V adj c).1
  have := (pull_exact F V adj c).2
  let d := derivedPull F V adj c
  let P := pull F c
  let W := HomologicalComplex.quasiIso (Mod R) (.up ℤ)
  have : d.functor.IsLeftDerivedFunctor d.comparison W := d.universal
  have : P.mapDerivedCategory.IsLeftDerivedFunctor P.mapDerivedCategoryFactors.hom W :=
    Functor.isLeftDerivedFunctor_of_inverts W _ P.mapDerivedCategoryFactors
  exact Functor.leftDerivedUnique P.mapDerivedCategory d.functor d.comparison
    P.mapDerivedCategoryFactors.hom W

end CategoryTheory.ConstantCompletion

namespace CategoryTheory.ExactKoszulTransport
set_option backward.isDefEq.respectTransparency true
set_option synthInstance.maxSize 2048
set_option backward.defeqAttrib.useBackward true
variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
private abbrev Modules (O : Sheaf J CommRingCat.{u}) := ConstantCompletion.Mod O
private abbrev Towers (O : Sheaf J CommRingCat.{u}) := ℕᵒᵖ ⥤ Modules O
private abbrev limitComplex (O : Sheaf J CommRingCat.{u}) :=
  (lim : Towers O ⥤ Modules O).mapHomologicalComplex (.up ℤ)
-- Reuse the proved generic unit-naturality API from the scalar-comparison module.
open _root_.CategoryTheory.FlatScalarKoszul
  (derivedUnitNat derivedUnitNat_app unit_app_Q unit_naturality)

attribute [local irreducible] ringedKoszulTensor ringedKoszulDualTower
  ringedKoszulDiagram SheafOfModules.monoidalCategory
attribute [local irreducible] Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors
  RingedKoszulLimitPresentation.unit
  RingedKoszulLimitPresentation.unitOnComplex

section Transport
variable {E : Type u} [SmallCategory E] {K : GrothendieckTopology E}
  (R : Sheaf J CommRingCat.{u}) (S : Sheaf K CommRingCat.{u})
  [HasDerivedCategory.{w} (ConstantCompletion.Mod R)]
  [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ ConstantCompletion.Mod R)]
  [HasDerivedCategory.{w} (ConstantCompletion.Mod S)]
  [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ ConstantCompletion.Mod S)]
  (P : ConstantCompletion.Mod R ⥤ ConstantCompletion.Mod S) [P.Additive]
  [PreservesFiniteLimits P] [PreservesFiniteColimits P]
  [PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ _ _).obj P)]
  [PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ _ _).obj P)]
  (r : ℕ) (b : Fin r → (R.obj ⋙ forget CommRingCat).sections)
  (a : Fin r → (S.obj ⋙ forget CommRingCat).sections)
  (DB : RingedKoszulLimitPresentation R r b)
  (DR : RingedKoszulLimitPresentation S r a)

omit [PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ _ _).obj P)]
  [PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ _ _).obj P)] in
private theorem unitCompatibility_of_Q
    (gamma : DB.completion ⋙ (P.mapDerivedCategory) ≅ (P.mapDerivedCategory) ⋙ DR.completion)
    (hq : ∀ N : ringedSiteComplex R,
      (P.mapDerivedCategory).map (DB.unitOnComplex N) ≫
          gamma.hom.app (DerivedCategory.Q.obj N) ≫
          DR.completion.map (P.mapDerivedCategoryFactors.hom.app N) =
        P.mapDerivedCategoryFactors.hom.app N ≫
          DR.unitOnComplex ((P.mapHomologicalComplex (.up ℤ)).obj N))
    (E : ringedSiteDerived R) :
    (P.mapDerivedCategory).map (DB.unit E) ≫ gamma.hom.app E =
      DR.unit ((P.mapDerivedCategory).obj E) := by
  let t₁ : (P.mapDerivedCategory) ⟶ (P.mapDerivedCategory) ⋙ DR.completion :=
    (P.mapDerivedCategory).leftUnitor.inv ≫
      Functor.whiskerRight (derivedUnitNat R DB) (P.mapDerivedCategory) ≫ gamma.hom
  let t₂ : (P.mapDerivedCategory) ⟶ (P.mapDerivedCategory) ⋙ DR.completion :=
    (P.mapDerivedCategory).rightUnitor.inv ≫
      Functor.whiskerLeft (P.mapDerivedCategory) (derivedUnitNat S DR)
  have ht : t₁ = t₂ := by
    apply Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso (Modules R) (.up ℤ))
    intro N
    dsimp only [t₁, t₂, NatTrans.comp_app, Functor.leftUnitor_inv_app,
      Functor.rightUnitor_inv_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
    simp only [Category.id_comp, derivedUnitNat_app]
    apply (cancel_mono (DR.completion.map
      (P.mapDerivedCategoryFactors.hom.app N))).mp
    rw [unit_app_Q]
    have hn := unit_naturality S DR (P.mapDerivedCategoryFactors.hom.app N)
    erw [← hn, unit_app_Q]
    simpa only [Category.assoc] using hq N
  simpa only [t₁, t₂, NatTrans.comp_app, Functor.leftUnitor_inv_app,
    Functor.rightUnitor_inv_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Category.id_comp, derivedUnitNat_app] using NatTrans.congr_app ht E

-- Descend the strict tower comparison, retaining its factorization equation.
private theorem descendedTensorComparison
    (h : ringedKoszulTensorTowerFunctor R r b ⋙
        (((Functor.whiskeringRight ℕᵒᵖ _ _).obj P).mapHomologicalComplex (.up ℤ)) ≅
        (P.mapHomologicalComplex (.up ℤ)) ⋙ ringedKoszulTensorTowerFunctor S r a) :
    ∃ hD : DB.tensorTower ⋙ (((Functor.whiskeringRight ℕᵒᵖ _ _).obj P).mapDerivedCategory) ≅
      (P.mapDerivedCategory) ⋙ DR.tensorTower,
      ∀ N : ringedSiteComplex R,
        (((Functor.whiskeringRight ℕᵒᵖ _ _).obj P).mapDerivedCategory).map
          (DB.tensorFactors.hom.app N) ≫
            ((Functor.whiskeringRight ℕᵒᵖ _ _).obj P).mapDerivedCategoryFactors.hom.app
              ((ringedKoszulTensorTowerFunctor R r b).obj N) ≫
            DerivedCategory.Q.map (h.hom.app N) =
          hD.hom.app (DerivedCategory.Q.obj N) ≫
            DR.tensorTower.map (P.mapDerivedCategoryFactors.hom.app N) ≫
            DR.tensorFactors.hom.app ((P.mapHomologicalComplex (.up ℤ)).obj N) := by
  let TB := ringedKoszulTensorTowerFunctor R r b
  let TR := ringedKoszulTensorTowerFunctor S r a
  let F := DB.tensorTower ⋙ (((Functor.whiskeringRight ℕᵒᵖ _ _).obj P).mapDerivedCategory)
  let G := (P.mapDerivedCategory) ⋙ DR.tensorTower
  let e : DerivedCategory.Q ⋙ F ≅ DerivedCategory.Q ⋙ G :=
    Functor.isoWhiskerRight DB.tensorFactors
      (((Functor.whiskeringRight ℕᵒᵖ _ _).obj P).mapDerivedCategory) ≪≫
    Functor.isoWhiskerLeft TB ((Functor.whiskeringRight ℕᵒᵖ _ _).obj P).mapDerivedCategoryFactors ≪≫
    Functor.isoWhiskerRight h DerivedCategory.Q ≪≫
    Functor.isoWhiskerLeft (P.mapHomologicalComplex (.up ℤ)) DR.tensorFactors.symm ≪≫
    Functor.isoWhiskerRight P.mapDerivedCategoryFactors.symm DR.tensorTower
  let ff := Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Q
    (HomologicalComplex.quasiIso (Modules R) (.up ℤ)) (DerivedCategory.{w} (Towers S))
  let hD : F ≅ G := ff.preimageIso e
  refine ⟨hD, ?_⟩
  intro N
  have he : hD.hom.app (DerivedCategory.Q.obj N) = e.hom.app N :=
    NatTrans.congr_app (ff.map_preimage e.hom) N
  rw [he]
  simp only [e, Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Category.assoc, ← Functor.map_comp_assoc,
    Iso.inv_hom_id_app, Functor.map_id]
  erw [Category.id_comp, Iso.inv_hom_id_app, Category.comp_id]

omit [HasDerivedCategory (ConstantCompletion.Mod R)]
  [HasDerivedCategory (ℕᵒᵖ ⥤ ConstantCompletion.Mod R)]
  [HasDerivedCategory (ConstantCompletion.Mod S)]
  [HasDerivedCategory (ℕᵒᵖ ⥤ ConstantCompletion.Mod S)]
  [PreservesFiniteLimits P] [PreservesFiniteColimits P]
  [PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ _ _).obj P)]
  [PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ _ _).obj P)] in
private theorem ordinaryUnitComparison
    (h : ringedKoszulTensorTowerFunctor R r b ⋙
        (((Functor.whiskeringRight ℕᵒᵖ _ _).obj P).mapHomologicalComplex (.up ℤ)) ≅
      (P.mapHomologicalComplex (.up ℤ)) ⋙ ringedKoszulTensorTowerFunctor S r a)
    (hu : ∀ (N : ringedSiteComplex R) (m : ℕᵒᵖ) (n : ℤ),
      P.map ((ringedKoszulTensorUnitComponent R r b N m).f n) ≫
        ((h.hom.app N).f n).app m =
      (ringedKoszulTensorUnitComponent S r a ((P.mapHomologicalComplex (.up ℤ)).obj N) m).f n)
    (beta : ∀ X : CochainComplex (Towers R) ℤ,
      (P.mapHomologicalComplex (.up ℤ)).obj ((limitComplex R).obj X) ≅
        (limitComplex S).obj ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj P).mapHomologicalComplex
          (.up ℤ)).obj X))
    (hb : ∀ X n m, ((beta X).hom.f n) ≫ limit.π _ m = P.map (limit.π (X.X n) m))
    (N : ringedSiteComplex R) :
    (P.mapHomologicalComplex (.up ℤ)).map (ringedKoszulLimitUnit R r b N) ≫
      (beta ((ringedKoszulTensorTowerFunctor R r b).obj N)).hom ≫
      (limitComplex S).map (h.hom.app N) =
        ringedKoszulLimitUnit S r a ((P.mapHomologicalComplex (.up ℤ)).obj N) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply limit.hom_ext
  intro m
  change (P.map (ringedKoszulLimitUnitF R r b N n) ≫ _ ≫
    limMap ((h.hom.app N).f n)) ≫ _ = _
  simp only [Category.assoc, limMap_π]
  erw [← Category.assoc _ (limit.π _ m), hb]
  erw [← P.map_comp_assoc]
  simp only [ringedKoszulLimitUnitF, id_eq]
  erw [limit.lift_π, limit.lift_π]
  exact hu N m n

-- Normalize the dependent endpoints of the tower and localization comparisons.
private theorem derivedUnitOnComplex
    (h : ringedKoszulTensorTowerFunctor R r b ⋙
        (((Functor.whiskeringRight ℕᵒᵖ _ _).obj P).mapHomologicalComplex (.up ℤ)) ≅
        (P.mapHomologicalComplex (.up ℤ)) ⋙ ringedKoszulTensorTowerFunctor S r a)
    (hD : DB.tensorTower ⋙ (((Functor.whiskeringRight ℕᵒᵖ _ _).obj P).mapDerivedCategory) ≅
      (P.mapDerivedCategory) ⋙ DR.tensorTower)
    (hd : ∀ N : ringedSiteComplex R,
      (((Functor.whiskeringRight ℕᵒᵖ _ _).obj P).mapDerivedCategory).map
          (DB.tensorFactors.hom.app N) ≫
          ((Functor.whiskeringRight ℕᵒᵖ _ _).obj P).mapDerivedCategoryFactors.hom.app
            ((ringedKoszulTensorTowerFunctor R r b).obj N) ≫
          DerivedCategory.Q.map (h.hom.app N) =
        hD.hom.app (DerivedCategory.Q.obj N) ≫
          DR.tensorTower.map (P.mapDerivedCategoryFactors.hom.app N) ≫
          DR.tensorFactors.hom.app ((P.mapHomologicalComplex (.up ℤ)).obj N))
    (beta : ∀ X : CochainComplex (Towers R) ℤ,
      (P.mapHomologicalComplex (.up ℤ)).obj ((limitComplex R).obj X) ≅
        (limitComplex S).obj ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj P).mapHomologicalComplex
          (.up ℤ)).obj X))
    (hb : ∀ X n m, ((beta X).hom.f n) ≫ limit.π _ m = P.map (limit.π (X.X n) m))
    (alpha : DB.inverseLimit ⋙ (P.mapDerivedCategory) ≅
      (((Functor.whiskeringRight ℕᵒᵖ _ _).obj P).mapDerivedCategory) ⋙ DR.inverseLimit)
    (ha : ∀ X : CochainComplex (Towers R) ℤ,
      (P.mapDerivedCategory).map (DB.comparison.app X) ≫
          alpha.hom.app (DerivedCategory.Q.obj X) =
        P.mapDerivedCategoryFactors.hom.app ((limitComplex R).obj X) ≫
          DerivedCategory.Q.map (beta X).hom ≫
          DR.comparison.app ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj P).mapHomologicalComplex
            (.up ℤ)).obj X) ≫
          DR.inverseLimit.map
            (((Functor.whiskeringRight ℕᵒᵖ _ _).obj P).mapDerivedCategoryFactors.inv.app X))
    (hu : ∀ (N : ringedSiteComplex R) (m : ℕᵒᵖ) (n : ℤ),
      P.map
          ((ringedKoszulTensorUnitComponent R r b N m).f n) ≫
          ((h.hom.app N).f n).app m =
        (ringedKoszulTensorUnitComponent S r a ((P.mapHomologicalComplex (.up ℤ)).obj N) m).f n)
    (N : ringedSiteComplex R) :
    (P.mapDerivedCategory).map (DB.unitOnComplex N) ≫
        alpha.hom.app (DB.tensorTower.obj (DerivedCategory.Q.obj N)) ≫
        DR.inverseLimit.map (hD.hom.app (DerivedCategory.Q.obj N)) ≫
        DR.completion.map (P.mapDerivedCategoryFactors.hom.app N) =
      P.mapDerivedCategoryFactors.hom.app N ≫
        DR.unitOnComplex ((P.mapHomologicalComplex (.up ℤ)).obj N) := by
  apply (cancel_mono
    (DR.inverseLimit.map (DR.tensorFactors.hom.app ((P.mapHomologicalComplex (.up ℤ)).obj N)))).mp
  have ht := congrArg DR.inverseLimit.map (hd N)
  have hn := alpha.hom.naturality (DB.tensorFactors.hom.app N)
  dsimp only [Functor.comp_map] at hn
  simp only [Functor.map_comp] at ht
  simp only [RingedKoszulLimitPresentation.unitOnComplex,
    Iso.app_inv,
    RingedKoszulLimitPresentation.completion, Functor.comp_map,
    Functor.map_comp, Category.assoc]
  rw [← ht, ← reassoc_of% hn]
  have hbi : (P.mapDerivedCategory).map (DB.inverseLimit.map (DB.tensorFactors.inv.app N)) ≫
      (P.mapDerivedCategory).map (DB.inverseLimit.map (DB.tensorFactors.hom.app N)) = 𝟙 _ := by
    rw [← Functor.map_comp, ← Functor.map_comp, Iso.inv_hom_id_app,
      Functor.map_id, Functor.map_id]
  have hri : DR.inverseLimit.map
        (DR.tensorFactors.inv.app ((P.mapHomologicalComplex (.up ℤ)).obj N)) ≫
      DR.inverseLimit.map
        (DR.tensorFactors.hom.app ((P.mapHomologicalComplex (.up ℤ)).obj N)) = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.inv_hom_id_app, Functor.map_id]
  erw [reassoc_of% hbi, hri]
  erw [reassoc_of% (ha ((ringedKoszulTensorTowerFunctor R r b).obj N))]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [DR.inverseLimit.map_id, Category.id_comp, Category.comp_id]
  have hv := P.mapDerivedCategoryFactors.hom.naturality
    (ringedKoszulLimitUnit R r b N)
  dsimp only [Functor.comp_map] at hv
  erw [reassoc_of% hv]
  have hc := DR.comparison.naturality (h.hom.app N)
  dsimp only [Functor.comp_map] at hc
  erw [← hc]
  have hq := congrArg DerivedCategory.Q.map
    (ordinaryUnitComparison R S P r b a h hu beta hb N)
  simp only [Functor.map_comp] at hq
  erw [reassoc_of% hq]
  rfl

private theorem assemble
    (h : ringedKoszulTensorTowerFunctor R r b ⋙
        (((Functor.whiskeringRight ℕᵒᵖ _ _).obj P).mapHomologicalComplex (.up ℤ)) ≅
      (P.mapHomologicalComplex (.up ℤ)) ⋙ ringedKoszulTensorTowerFunctor S r a)
    (hu : ∀ (N : ringedSiteComplex R) (m : ℕᵒᵖ) (n : ℤ),
      P.map ((ringedKoszulTensorUnitComponent R r b N m).f n) ≫
        ((h.hom.app N).f n).app m =
      (ringedKoszulTensorUnitComponent S r a ((P.mapHomologicalComplex (.up ℤ)).obj N) m).f n)
    (beta : ∀ X : CochainComplex (Towers R) ℤ,
      (P.mapHomologicalComplex (.up ℤ)).obj ((limitComplex R).obj X) ≅
        (limitComplex S).obj ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj P).mapHomologicalComplex
          (.up ℤ)).obj X))
    (hb : ∀ X n m, ((beta X).hom.f n) ≫ limit.π _ m = P.map (limit.π (X.X n) m))
    (alpha : DB.inverseLimit ⋙ (P.mapDerivedCategory) ≅
      (((Functor.whiskeringRight ℕᵒᵖ _ _).obj P).mapDerivedCategory) ⋙ DR.inverseLimit)
    (ha : ∀ X : CochainComplex (Towers R) ℤ,
      (P.mapDerivedCategory).map (DB.comparison.app X) ≫ alpha.hom.app (DerivedCategory.Q.obj X) =
        P.mapDerivedCategoryFactors.hom.app ((limitComplex R).obj X) ≫
          DerivedCategory.Q.map (beta X).hom ≫
          DR.comparison.app ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj P).mapHomologicalComplex
            (.up ℤ)).obj X) ≫
          DR.inverseLimit.map
            (((Functor.whiskeringRight ℕᵒᵖ _ _).obj P).mapDerivedCategoryFactors.inv.app X)) :
    ∃ gamma : DB.completion ⋙ (P.mapDerivedCategory) ≅ (P.mapDerivedCategory) ⋙ DR.completion,
      ∀ M, (P.mapDerivedCategory).map (DB.unit M) ≫ gamma.hom.app M =
        DR.unit ((P.mapDerivedCategory).obj M) := by
  obtain ⟨hD, hd⟩ := descendedTensorComparison R S P r b a DB DR h
  let gamma : DB.completion ⋙ (P.mapDerivedCategory) ≅ (P.mapDerivedCategory) ⋙ DR.completion :=
    Functor.isoWhiskerLeft DB.tensorTower alpha ≪≫
      Functor.isoWhiskerRight hD DR.inverseLimit
  have hg (E : ringedSiteDerived R) :
      gamma.hom.app E = alpha.hom.app (DB.tensorTower.obj E) ≫
        DR.inverseLimit.map (hD.hom.app E) := by
    simp only [gamma, RingedKoszulLimitPresentation.completion, Functor.comp_obj,
      Iso.trans_hom, NatTrans.comp_app,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      Functor.whiskerLeft_app, Functor.whiskerRight_app]
  refine ⟨gamma, ?_⟩
  intro E
  apply unitCompatibility_of_Q R S P r b a DB DR gamma _ E
  intro N
  rw [hg]
  simpa only [RingedKoszulLimitPresentation.completion, Functor.comp_obj, Category.assoc] using
    derivedUnitOnComplex R S P r b a DB DR h hD hd beta hb alpha ha hu N

end Transport
end CategoryTheory.ExactKoszulTransport

namespace CategoryTheory.ConstantCompletion

-- The concrete final calculation respects the protected choices and uses only naturality.
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] pullDerivedIso pull RingedKoszulLimitPresentation.unit
  RingedKoszulLimitPresentation.completion Functor.mapDerivedCategory
  Functor.mapDerivedCategoryFactors ringedKoszulTensor ringedKoszulDualTower
  ringedKoszulDiagram SheafOfModules.monoidalCategory

/-- Exact inverse image preserving countable products transports the actual Koszul unit.

Source: Stacks Project, algebraization.tex, Tag 0A0E, proof by the augmented finite
Koszul tower; sites-cohomology.tex, Tags 07A4 and 0941.
(auxiliary; not a blueprint node).

Proof: the coefficient isomorphism identifies pure module inverse image with the
specified module pullback. This is additive and exact. Forgetting module structure
computes products, so the assumed product preservation on sheaves gives invertible
canonical product comparisons on modules. The canonical tensor comparison identifies
pullback of each rank-one Koszul factor with the corresponding factor over the target
ring. Naturality of the constant-ring comparison identifies the scalar powers and the
transitions. Iterating tensor comparison gives an isomorphism of strict tensor towers,
natural in the complex, carrying the degree-zero augmentation to the target
augmentation. Since the module functor is exact, it inverts quasi-isomorphisms and its
left derived comparison is invertible on every complex. The strict Roos comparison
computes inverse limit by the shifted cone of one minus the shift. The product
comparison intertwines the shift by its projection formula and preserves both summands
of the cone. It carries the augmentation with coordinates (gamma, zero) to the target
augmentation with those same coordinates. Descend the tower isomorphism and this
normalized cone comparison through localization. Uniqueness of the derived tensor
tower and of derived inverse limit identifies the resulting functors with the supplied
presentations. Their prescribed units are defined by precisely these augmentations,
which proves the displayed unit equation. For no generators the sole factor is the
unit complex; zero scalars, units, and zero coefficient rings satisfy the same formulas.
-/
theorem exactCompletedKoszulPullback
    {C D : Type v} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {L : Sheaf J (Type v) ⥤ Sheaf K (Type v)}
    (F : InverseImageData L) (V : Sheaf K (Type v) ⥤ Sheaf J (Type v))
    (adj : L ⊣ V) [PreservesFiniteLimits L]
    [PreservesLimitsOfShape (Discrete ℕ) L]
    (A : Type v) [CommRing A] (I : Ideal A)
    [IsIso (completedMap F A I)]
    [HasExactLimitsOfShape (Discrete ℕ) (Mod (completed J A I))]
    [HasExactLimitsOfShape (Discrete ℕ) (Mod (completed K A I))]
    (r : ℕ) (a : Fin r → A)
    (PX : KoszulPresentation J A I true r a)
    (PS : KoszulPresentation K A I true r a) :
    ∃ e : koszulCompletion J A I PX ⋙ (derivedPull F V adj (completedMap F A I)).functor ≅
        (derivedPull F V adj (completedMap F A I)).functor ⋙ koszulCompletion K A I PS,
      ∀ M, (derivedPull F V adj (completedMap F A I)).functor.map
          (koszulUnit J A I PX M) ≫ e.hom.app M =
        koszulUnit K A I PS ((derivedPull F V adj (completedMap F A I)).functor.obj M) := by
  classical
  let := HasDerivedCategory.standard (Mod (coefficients J A I true))
  let := HasDerivedCategory.standard (Mod (coefficients K A I true))
  let := HasDerivedCategory.standard (ℕᵒᵖ ⥤ Mod (coefficients J A I true))
  let := HasDerivedCategory.standard (ℕᵒᵖ ⥤ Mod (coefficients K A I true))
  let := HasDerivedCategory.standard (Mod (completed J A I))
  let := HasDerivedCategory.standard (Mod (completed K A I))
  let := HasDerivedCategory.standard (ℕᵒᵖ ⥤ Mod (completed J A I))
  let := HasDerivedCategory.standard (ℕᵒᵖ ⥤ Mod (completed K A I))
  let P := pull F (completedMap F A I)
  have : PreservesFiniteLimits P := (pull_exact F V adj _).1
  have : PreservesFiniteColimits P := (pull_exact F V adj _).2
  have : PreservesLimitsOfShape (Discrete ℕ) P := pull_products F _
  have : PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ _ _).obj P) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  have : PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ _ _).obj P) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  have : IsGrothendieckAbelian.{v} (Mod (completed J A I)) :=
    SheafOfModules.isGrothendieckAbelian _
  have : IsGrothendieckAbelian.{v} (Mod (completed K A I)) :=
    SheafOfModules.isGrothendieckAbelian _
  have : IsGrothendieckAbelian.{v} (ℕᵒᵖ ⥤ Mod (completed J A I)) := towerGrothendieck
  have : IsGrothendieckAbelian.{v} (ℕᵒᵖ ⥤ Mod (completed K A I)) := towerGrothendieck
  let etaX := Functor.whiskerRight (ordinaryLimitIso (A := Mod (completed J A I))).inv
    DerivedCategory.Q.{v+1} ≫ PX.comparison
  let etaS := Functor.whiskerRight (ordinaryLimitIso (A := Mod (completed K A I))).inv
    DerivedCategory.Q.{v+1} ≫ PS.comparison
  have hx : PX.inverseLimit.IsRightDerivedFunctor etaX
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ Mod (coefficients J A I true)) (.up ℤ)) := by
    rw [Functor.isRightDerivedFunctor_iff_isLeftKanExtension]
    have := PX.isRightDerived
    have : PX.inverseLimit.IsLeftKanExtension PX.comparison :=
      Functor.IsRightDerivedFunctor.isLeftKanExtension _ _
        (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ Mod (coefficients J A I true)) (.up ℤ))
    apply (Functor.isLeftKanExtension_iff_of_iso₂ PX.comparison etaX
      (Functor.isoWhiskerRight (ordinaryLimitIso (A := Mod (completed J A I)))
        DerivedCategory.Q.{v+1})
      (Iso.refl _) ?_).mp inferInstance
    rw [Iso.refl_hom, Functor.whiskerLeft_id', Category.comp_id]
    change PX.comparison =
      (Functor.isoWhiskerRight (ordinaryLimitIso (A := Mod (completed J A I)))
        DerivedCategory.Q.{v+1}).hom ≫
      (Functor.isoWhiskerRight (ordinaryLimitIso (A := Mod (completed J A I)))
        DerivedCategory.Q.{v+1}).inv ≫ PX.comparison
    rw [Iso.hom_inv_id_assoc]
  have hs : PS.inverseLimit.IsRightDerivedFunctor etaS
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ Mod (coefficients K A I true)) (.up ℤ)) := by
    rw [Functor.isRightDerivedFunctor_iff_isLeftKanExtension]
    have := PS.isRightDerived
    have : PS.inverseLimit.IsLeftKanExtension PS.comparison :=
      Functor.IsRightDerivedFunctor.isLeftKanExtension _ _
        (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ Mod (coefficients K A I true)) (.up ℤ))
    apply (Functor.isLeftKanExtension_iff_of_iso₂ PS.comparison etaS
      (Functor.isoWhiskerRight (ordinaryLimitIso (A := Mod (completed K A I)))
        DerivedCategory.Q.{v+1})
      (Iso.refl _) ?_).mp inferInstance
    rw [Iso.refl_hom, Functor.whiskerLeft_id', Category.comp_id]
    change PS.comparison =
      (Functor.isoWhiskerRight (ordinaryLimitIso (A := Mod (completed K A I)))
        DerivedCategory.Q.{v+1}).hom ≫
      (Functor.isoWhiskerRight (ordinaryLimitIso (A := Mod (completed K A I)))
        DerivedCategory.Q.{v+1}).inv ≫ PS.comparison
    rw [Iso.hom_inv_id_assoc]
  have hl := exactProductFunctorStrictLimit.{v, v, v, v, v, v, v+1, v+1}
    J (siteModuleRings (completed J A I)) K (siteModuleRings (completed K A I))
    (fun U x y ↦ @mul_comm ((completed J A I).obj.obj U) _ x y)
    (fun U x y ↦ @mul_comm ((completed K A I).obj.obj U) _ x y)
    P (fun M ↦ inferInstance) PX.inverseLimit PS.inverseLimit etaX hx etaS hs
  choose beta alpha hlimit using normalizedActualLimit P PX.inverseLimit PS.inverseLimit
    PX.comparison PS.comparison hl
  have hb := hlimit.1
  have ha := hlimit.2
  choose hT hU using strictCompletedKoszulTowerPullback F V adj A I r a
  choose gamma hg using ExactKoszulTransport.assemble
    (completed J A I) (completed K A I) P r
    (fun i ↦ algebraSection (baseMap J A I true) (a i))
    (fun i ↦ algebraSection (baseMap K A I true) (a i))
    PX PS hT hU beta hb alpha ha
  let delta := pullDerivedIso F V adj (completedMap F A I)
  let e : PX.completion ⋙ (derivedPull F V adj (completedMap F A I)).functor ≅
      (derivedPull F V adj (completedMap F A I)).functor ⋙ PS.completion :=
    Functor.isoWhiskerLeft PX.completion delta ≪≫ gamma ≪≫
      Functor.isoWhiskerRight delta.symm PS.completion
  refine ⟨e, ?_⟩
  intro M
  change (derivedPull F V adj (completedMap F A I)).functor.map (PX.unit M) ≫
    e.hom.app M = PS.unit ((derivedPull F V adj (completedMap F A I)).functor.obj M)
  have hn := delta.hom.naturality (PX.unit M)
  have hu := FlatScalarKoszul.unit_naturality (completed K A I) PS (delta.inv.app M)
  dsimp only [e, Iso.trans_hom, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Iso.symm_hom, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  rw [reassoc_of% hn, reassoc_of% (hg M)]
  rw [← hu, ← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]

end CategoryTheory.ConstantCompletion
