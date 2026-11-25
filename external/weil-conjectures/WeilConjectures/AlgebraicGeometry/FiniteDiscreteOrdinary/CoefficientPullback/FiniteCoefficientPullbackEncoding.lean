/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteCoefficientOperationEncoding
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar

import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.CoefficientPullback.FiniteCoefficientHeartPullbackComposition
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import all WeilConjectures.CategoryTheory.Derived.DerivedExactCube

/-! # Composition-compatible coefficient encoding of inverse images

This is the inverse-image part of normalized coefficient transport. It involves
neither direct images nor exchange morphisms.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

open CategoryTheory.Functor
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

section
variable {C₀ C₁ C₂ D₀ D₁ D₂ : Type*}
  [Category C₀] [Category C₁] [Category C₂]
  [Category D₀] [Category D₁] [Category D₂]
  {U₀ : C₀ ⥤ C₂} {U₁ : C₀ ⥤ C₁} {U₂ : C₁ ⥤ C₂}
  {V₀ : D₀ ⥤ D₂} {V₁ : D₀ ⥤ D₁} {V₂ : D₁ ⥤ D₂}
  {F₀ F₀' : C₀ ⥤ D₀} {F₁ F₁' : C₁ ⥤ D₁} {F₂ F₂' : C₂ ⥤ D₂}

private def vertexSquare (p : U₀ ⋙ F₂ ≅ F₀ ⋙ V₀)
    (c₀ : F₀ ≅ F₀') (c₂ : F₂ ≅ F₂') : U₀ ⋙ F₂' ≅ F₀' ⋙ V₀ :=
  Functor.isoWhiskerLeft U₀ c₂.symm ≪≫ p ≪≫ Functor.isoWhiskerRight c₀ V₀

private lemma vertex_comp
    (cU : U₀ ≅ U₁ ⋙ U₂) (cV : V₀ ≅ V₁ ⋙ V₂)
    (p₀ : U₀ ⋙ F₂ ≅ F₀ ⋙ V₀) (p₁ : U₁ ⋙ F₁ ≅ F₀ ⋙ V₁)
    (p₂ : U₂ ⋙ F₂ ≅ F₁ ⋙ V₂)
    (c₀ : F₀ ≅ F₀') (c₁ : F₁ ≅ F₁') (c₂ : F₂ ≅ F₂')
    (h : ∀ M, F₂.map (cU.hom.app M) ≫ p₂.hom.app (U₁.obj M) ≫
      V₂.map (p₁.hom.app M) = p₀.hom.app M ≫ cV.hom.app (F₀.obj M)) (M : C₀) :
    F₂'.map (cU.hom.app M) ≫ (vertexSquare p₂ c₁ c₂).hom.app (U₁.obj M) ≫
      V₂.map ((vertexSquare p₁ c₀ c₁).hom.app M) =
    (vertexSquare p₀ c₀ c₂).hom.app M ≫ cV.hom.app (F₀'.obj M) := by
  simp only [vertexSquare, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.map_comp, Category.assoc]
  erw [reassoc_of% (c₂.inv.naturality (cU.hom.app M))]
  rw [← V₂.map_comp_assoc, Iso.hom_inv_id_app, V₂.map_id, Category.id_comp]
  rw [reassoc_of% h, cV.hom.naturality]
  rfl

variable {U₀' : C₀ ⥤ C₂} {U₁' : C₀ ⥤ C₁} {U₂' : C₁ ⥤ C₂}
  {V₀' : D₀ ⥤ D₂} {V₁' : D₀ ⥤ D₁} {V₂' : D₁ ⥤ D₂}

private def edgeSquare (p : U₀ ⋙ F₂ ≅ F₀ ⋙ V₀)
    (s : U₀' ≅ U₀) (t : V₀' ≅ V₀) : U₀' ⋙ F₂ ≅ F₀ ⋙ V₀' :=
  Functor.isoWhiskerRight s F₂ ≪≫ p ≪≫ Functor.isoWhiskerLeft F₀ t.symm

private lemma edge_comp
    (cU : U₀ ≅ U₁ ⋙ U₂) (cV : V₀ ≅ V₁ ⋙ V₂)
    (cU' : U₀' ≅ U₁' ⋙ U₂') (cV' : V₀' ≅ V₁' ⋙ V₂')
    (p₀ : U₀ ⋙ F₂ ≅ F₀ ⋙ V₀) (p₁ : U₁ ⋙ F₁ ≅ F₀ ⋙ V₁)
    (p₂ : U₂ ⋙ F₂ ≅ F₁ ⋙ V₂)
    (s₀ : U₀' ≅ U₀) (s₁ : U₁' ≅ U₁) (s₂ : U₂' ≅ U₂)
    (t₀ : V₀' ≅ V₀) (t₁ : V₁' ≅ V₁) (t₂ : V₂' ≅ V₂)
    (hs : ∀ M, cU'.hom.app M ≫ U₂'.map (s₁.hom.app M) ≫
      s₂.hom.app (U₁.obj M) = s₀.hom.app M ≫ cU.hom.app M)
    (ht : ∀ N, cV'.hom.app N ≫ V₂'.map (t₁.hom.app N) ≫
      t₂.hom.app (V₁.obj N) = t₀.hom.app N ≫ cV.hom.app N)
    (h : ∀ M, F₂.map (cU.hom.app M) ≫ p₂.hom.app (U₁.obj M) ≫
      V₂.map (p₁.hom.app M) = p₀.hom.app M ≫ cV.hom.app (F₀.obj M)) (M : C₀) :
    F₂.map (cU'.hom.app M) ≫ (edgeSquare p₂ s₂ t₂).hom.app (U₁'.obj M) ≫
      V₂'.map ((edgeSquare p₁ s₁ t₁).hom.app M) =
    (edgeSquare p₀ s₀ t₀).hom.app M ≫ cV'.hom.app (F₀.obj M) := by
  apply (cancel_mono (V₂'.map (t₁.hom.app (F₀.obj M)) ≫
    t₂.hom.app (V₁.obj (F₀.obj M)))).mp
  simp only [edgeSquare, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.map_comp, Category.assoc]
  rw [← V₂'.map_comp_assoc (t₁.inv.app (F₀.obj M)) (t₁.hom.app (F₀.obj M)),
    Iso.inv_hom_id_app, V₂'.map_id, Category.id_comp]
  erw [t₂.hom.naturality (p₁.hom.app M),
    reassoc_of% (t₂.hom.naturality (F₁.map (s₁.hom.app M)))]
  simp only [Functor.comp_obj]
  rw [Iso.inv_hom_id_app_assoc]
  rw [← reassoc_of% p₂.hom.naturality]
  rw [← F₂.map_comp_assoc (s₂.hom.app (U₁'.obj M))
    (U₂.map (s₁.hom.app M)), ← s₂.hom.naturality]
  rw [← F₂.map_comp_assoc, hs, F₂.map_comp]
  rw [Category.assoc, h]
  rw [ht]
  simp only [Iso.inv_hom_id_app_assoc]
end

section
variable {C₀ C₁ C₂ D₀ D₁ D₂ : Type*}
  [Category C₀] [Category C₁] [Category C₂]
  [Category D₀] [Category D₁] [Category D₂]
  [Abelian C₀] [Abelian C₁] [Abelian C₂]
  [Abelian D₀] [Abelian D₁] [Abelian D₂]
  [HasDerivedCategory C₀] [HasDerivedCategory C₁] [HasDerivedCategory C₂]
  [HasDerivedCategory D₀] [HasDerivedCategory D₁] [HasDerivedCategory D₂]
  (U₀ : C₀ ⥤ C₂) (U₁ : C₀ ⥤ C₁) (U₂ : C₁ ⥤ C₂)
  (V₀ : D₀ ⥤ D₂) (V₁ : D₀ ⥤ D₁) (V₂ : D₁ ⥤ D₂)
  (F₀ : C₀ ⥤ D₀) (F₁ : C₁ ⥤ D₁) (F₂ : C₂ ⥤ D₂)
  [U₀.Additive] [PreservesFiniteLimits U₀] [PreservesFiniteColimits U₀]
  [U₁.Additive] [PreservesFiniteLimits U₁] [PreservesFiniteColimits U₁]
  [U₂.Additive] [PreservesFiniteLimits U₂] [PreservesFiniteColimits U₂]
  [V₀.Additive] [PreservesFiniteLimits V₀] [PreservesFiniteColimits V₀]
  [V₁.Additive] [PreservesFiniteLimits V₁] [PreservesFiniteColimits V₁]
  [V₂.Additive] [PreservesFiniteLimits V₂] [PreservesFiniteColimits V₂]
  [F₀.Additive] [PreservesFiniteLimits F₀] [PreservesFiniteColimits F₀]
  [F₁.Additive] [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
  [F₂.Additive] [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]

private lemma triangle_fac (cU : U₀ ≅ U₁ ⋙ U₂) (K : CochainComplex C₀ ℤ) :
    (mapDerivedCategoryTriangleIso cU).hom.app (DerivedCategory.Q.obj K) ≫
      U₂.mapDerivedCategory.map (U₁.mapDerivedCategoryFactors.hom.app K) ≫
      U₂.mapDerivedCategoryFactors.hom.app
        ((U₁.mapHomologicalComplex (.up ℤ)).obj K) =
    U₀.mapDerivedCategoryFactors.hom.app K ≫ DerivedCategory.Q.map
      ((NatTrans.mapHomologicalComplex cU.hom (.up ℤ)).app K) := by
  simp only [mapDerivedCategoryTriangleIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Category.assoc]
  rw [comp_fac]
  exact mapDerivedCategoryNatIso_fac cU K

private lemma derived_comp
    (cU : U₀ ≅ U₁ ⋙ U₂) (cV : V₀ ≅ V₁ ⋙ V₂)
    (p₀ : U₀ ⋙ F₂ ≅ F₀ ⋙ V₀) (p₁ : U₁ ⋙ F₁ ≅ F₀ ⋙ V₁)
    (p₂ : U₂ ⋙ F₂ ≅ F₁ ⋙ V₂)
    (h : ∀ M, F₂.map (cU.hom.app M) ≫ p₂.hom.app (U₁.obj M) ≫
      V₂.map (p₁.hom.app M) = p₀.hom.app M ≫ cV.hom.app (F₀.obj M))
    (M : DerivedCategory C₀) :
    F₂.mapDerivedCategory.map ((mapDerivedCategoryTriangleIso cU).hom.app M) ≫
      (mapDerivedCategorySquareIso p₂).hom.app (U₁.mapDerivedCategory.obj M) ≫
      V₂.mapDerivedCategory.map ((mapDerivedCategorySquareIso p₁).hom.app M) =
    (mapDerivedCategorySquareIso p₀).hom.app M ≫
      (mapDerivedCategoryTriangleIso cV).hom.app (F₀.mapDerivedCategory.obj M) := by
  suffices hh : whiskerRight (mapDerivedCategoryTriangleIso cU).hom F₂.mapDerivedCategory ≫
      whiskerLeft U₁.mapDerivedCategory (mapDerivedCategorySquareIso p₂).hom ≫
      whiskerRight (mapDerivedCategorySquareIso p₁).hom V₂.mapDerivedCategory =
    (mapDerivedCategorySquareIso p₀).hom ≫
      whiskerLeft F₀.mapDerivedCategory (mapDerivedCategoryTriangleIso cV).hom from
    congr_app hh M
  apply Localization.natTrans_ext DerivedCategory.Q (HomologicalComplex.quasiIso C₀ (.up ℤ))
  intro K
  simp only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app]
  apply (cancel_mono
    (V₂.mapDerivedCategory.map (V₁.mapDerivedCategory.map
        (F₀.mapDerivedCategoryFactors.hom.app K)) ≫
      V₂.mapDerivedCategory.map (V₁.mapDerivedCategoryFactors.hom.app
        ((F₀.mapHomologicalComplex (.up ℤ)).obj K)) ≫
      V₂.mapDerivedCategoryFactors.hom.app
        ((V₁.mapHomologicalComplex (.up ℤ)).obj
          ((F₀.mapHomologicalComplex (.up ℤ)).obj K)))).mp
  have h₀ := face_fac U₀ F₂ F₀ V₀ p₀ K
  have h₁ := face_fac U₁ F₁ F₀ V₁ p₁ K
  have h₂ := face_fac U₂ F₂ F₁ V₂ p₂ ((U₁.mapHomologicalComplex (.up ℤ)).obj K)
  have n₂ := (mapDerivedCategorySquareIso p₂).hom.naturality
    (U₁.mapDerivedCategoryFactors.hom.app K)
  have nV := (mapDerivedCategoryTriangleIso cV).hom.naturality
    (F₀.mapDerivedCategoryFactors.hom.app K)
  dsimp only [Functor.comp_map] at n₂ nV
  have hL :
      F₂.mapDerivedCategory.map ((mapDerivedCategoryTriangleIso cU).hom.app
        (DerivedCategory.Q.obj K)) ≫
      (mapDerivedCategorySquareIso p₂).hom.app
        (U₁.mapDerivedCategory.obj (DerivedCategory.Q.obj K)) ≫
      V₂.mapDerivedCategory.map ((mapDerivedCategorySquareIso p₁).hom.app
        (DerivedCategory.Q.obj K)) ≫
      V₂.mapDerivedCategory.map (V₁.mapDerivedCategory.map
        (F₀.mapDerivedCategoryFactors.hom.app K)) ≫
      V₂.mapDerivedCategory.map (V₁.mapDerivedCategoryFactors.hom.app
        ((F₀.mapHomologicalComplex (.up ℤ)).obj K)) ≫
      V₂.mapDerivedCategoryFactors.hom.app
        ((V₁.mapHomologicalComplex (.up ℤ)).obj
          ((F₀.mapHomologicalComplex (.up ℤ)).obj K)) =
      F₂.mapDerivedCategory.map (U₀.mapDerivedCategoryFactors.hom.app K) ≫
      F₂.mapDerivedCategoryFactors.hom.app ((U₀.mapHomologicalComplex (.up ℤ)).obj K) ≫
      DerivedCategory.Q.map
        ((F₂.mapHomologicalComplex (.up ℤ)).map
          ((NatTrans.mapHomologicalComplex cU.hom (.up ℤ)).app K) ≫
        (NatTrans.mapHomologicalComplex p₂.hom (.up ℤ)).app
          ((U₁.mapHomologicalComplex (.up ℤ)).obj K) ≫
        (V₂.mapHomologicalComplex (.up ℤ)).map
          ((NatTrans.mapHomologicalComplex p₁.hom (.up ℤ)).app K)) := by
    erw [← V₂.mapDerivedCategory.map_comp_assoc, ← V₂.mapDerivedCategory.map_comp_assoc]
    simp only [Category.assoc]
    erw [h₁]
    simp only [Functor.map_comp, Category.assoc]
    erw [V₂.mapDerivedCategoryFactors_hom_naturality]
    erw [← reassoc_of% n₂, reassoc_of% h₂]
    erw [← F₂.mapDerivedCategory.map_comp_assoc, ← F₂.mapDerivedCategory.map_comp_assoc]
    simp only [Category.assoc]
    erw [triangle_fac U₀ U₁ U₂ cU K]
    simp only [Functor.map_comp, Category.assoc]
    erw [F₂.mapDerivedCategoryFactors_hom_naturality_assoc]
  simp only [Category.assoc]
  erw [hL]
  erw [← reassoc_of% nV, triangle_fac V₀ V₁ V₂ cV]
  erw [reassoc_of% h₀]
  simp only [← Functor.map_comp]
  repeat' apply congrArg (fun t ↦ _ ≫ t)
  apply congrArg DerivedCategory.Q.map
  ext n
  exact h (K.X n)
end

namespace AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary.CoefficientPullback

variable (A : Type u) [CommRing A] [Finite A]
  [TopologicalSpace A] [DiscreteTopology A] [IsTopologicalRing A]
variable (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj R] [IsCommMonObj R]

/-- The published total internal inverse image, with its scalar ring fixed.
Source: published internal derived inverse image
(blueprint: lem-sfb-finite-coefficient-pullback-encoding). -/
abbrev pull {X Y : Scheme.{u}} (f : X ⟶ Y) :
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj R Y)) ⥤
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj R X)) :=
  (fun {F G : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj R Y)) ⥤
        DerivedCategory
          (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj R X))}
      (_ : F ≅ G) ↦ F) (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory R f)

/-- The published total inverse image of fixed-scalar module sheaves.
Source: published fixed-scalar derived inverse image
(blueprint: lem-sfb-finite-coefficient-pullback-encoding). -/
abbrev fixedPull {X Y : Scheme.{u}} (f : X ⟶ Y) :
    DerivedCategory (Sheaf (Scheme.ProEt.topology Y)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) ⥤
    DerivedCategory (Sheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) :=
  (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f).leftDerivedFunctor

/-- A family of inverse-image comparisons, before imposing composition compatibility.
Source: the inverse-image part of normalized coefficient transport
(blueprint: lem-sfb-finite-coefficient-pullback-encoding). -/
abbrev Family (e : Mon.mk R ≅ Mon.mk (coefficient A))
    (E : ∀ T : Scheme.{u}, Encoding A T) :=
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    pull R f ⋙ coefficientEncoding A e X (E X) ≅
      coefficientEncoding A e Y (E Y) ⋙ fixedPull A f

private def heartDerivedIso (e : Mon.mk R ≅ Mon.mk (coefficient A))
    (T : Scheme.{u}) (E : Encoding A T) :
    (heart A R e T E).mapDerivedCategory ≅ coefficientEncoding A e T E :=
  mapDerivedCategoryNatIso (eqToIso (heart_eq A R e T E)) ≪≫
    (mapDerivedCategoryCompIso (Mod.comap (coefficientMap e.inv.hom T))
      (E.ordinary.functor ⋙ E.fixed.functor)).symm

private def localizedPull (e : Mon.mk R ≅ Mon.mk (coefficient A))
    (E : ∀ T : Scheme.{u}, Encoding A T) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (CondensedRing.upperStar R f).mapDerivedCategory ⋙
        (heart A R e X (E X)).mapDerivedCategory ≅
      (heart A R e Y (E Y)).mapDerivedCategory ⋙
        (upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f).mapDerivedCategory :=
  mapDerivedCategorySquareIso (heartPull A R e f (E X) (E Y))

private def normalizedPull (e : Mon.mk R ≅ Mon.mk (coefficient A))
    (E : ∀ T : Scheme.{u}, Encoding A T) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (CondensedRing.upperStar R f).mapDerivedCategory ⋙ coefficientEncoding A e X (E X) ≅
      coefficientEncoding A e Y (E Y) ⋙
        (upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f).mapDerivedCategory :=
  vertexSquare (localizedPull A R e E f) (heartDerivedIso A R e Y (E Y))
    (heartDerivedIso A R e X (E X))

private def totalPull (e : Mon.mk R ≅ Mon.mk (coefficient A))
    (E : ∀ T : Scheme.{u}, Encoding A T) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    pull R f ⋙ coefficientEncoding A e X (E X) ≅
      coefficientEncoding A e Y (E Y) ⋙ fixedPull A f :=
  edgeSquare (normalizedPull A R e E f)
    (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory R f)
    (leftDerivedUpperStarIsoMapDerivedCategory
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f)

private lemma internal_compositor {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj R Z))) :
    (CondensedRing.leftDerivedUpperStarComp R f g).hom.app M ≫
      (pull R f).map ((CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory R g).hom.app M) ≫
      (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory R f).hom.app
        ((CondensedRing.upperStar R g).mapDerivedCategory.obj M) =
    (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory R (f ≫ g)).hom.app M ≫
      (mapDerivedCategoryTriangleIso (CondensedRing.upperStarComp R f g)).hom.app M := by
  have hn := (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory R f).inv.naturality
    ((CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory R g).hom.app M)
  simp only [CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory] at hn ⊢
  simp only [CondensedRing.leftDerivedUpperStarComp, Functor.leftDerivedFunctorNatIso,
    Functor.leftDerivedFunctorCompIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Category.assoc, Iso.inv_hom_id_app_assoc,
    mapDerivedCategoryTriangleIso]
  rw [← reassoc_of% hn]
  simp only [Iso.inv_hom_id_app, Category.comp_id, ← Functor.map_comp,
    CategoryTheory.Functor.map_id]
  erw [Category.comp_id]

omit [Finite A] [DiscreteTopology A] [TopologicalSpace A] [IsTopologicalRing A] in
private lemma fixed_compositor {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology Z)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))) :
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f g).hom.app M ≫
      (fixedPull A f).map ((leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) g).hom.app M) ≫
      (leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f).hom.app
          ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) g).mapDerivedCategory.obj M) =
    (leftDerivedUpperStarIsoMapDerivedCategory
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) (f ≫ g)).hom.app M ≫
      (mapDerivedCategoryTriangleIso
        (upperStarComp (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f g)).hom.app M := by
  have hn := (leftDerivedUpperStarIsoMapDerivedCategory
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f).inv.naturality
      ((leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) g).hom.app M)
  simp only [leftDerivedUpperStarIsoMapDerivedCategory] at hn ⊢
  simp only [leftDerivedUpperStarComp, Functor.leftDerivedFunctorNatIso,
    Functor.leftDerivedFunctorCompIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Category.assoc, Iso.inv_hom_id_app_assoc,
    mapDerivedCategoryTriangleIso]
  rw [← reassoc_of% hn]
  simp only [Iso.inv_hom_id_app, Category.comp_id, ← Functor.map_comp,
    CategoryTheory.Functor.map_id]
  erw [Category.comp_id]

-- Retain the original finite-discrete interface, although the normalized encoding suffices.
set_option linter.unusedSectionVars false in
/-- Normalized encoding commutes with inverse images and their published compositors.

Source: blueprint proper-base-change-finite, Transport and clause (2);
lem-sfb-finite-coefficient-exchange-encoding, proof steps 1--2; Stacks 03D3 and 0D6D.
(blueprint: lem-sfb-finite-coefficient-pullback-encoding).

Proof: On hearts, restrict scalars along the inverse coefficient isomorphism,
apply section-action reconstruction and restrict to constant scalars. Scalar restriction
along an isomorphism commutes with direct image by the coefficient-map naturality
square. Section-action identifies the internal direct image with its sectionwise
ringed-site direct image. The normalized constant-section maps identify the latter
with direct image of fixed-scalar sheaves: both evaluate the same additive sheaf
on the same fibre product and have the same scalar action. This comparison is the
identity on underlying sections. For two successive morphisms these identities commute
with the canonical direct-image compositor, since the two fibre-product evaluations
are canonically identified. Conjugate these identity-on-sections comparisons under the
specified geometric adjunctions. The adjunction unit equation uniquely determines the
inverse-image comparisons and identifies their composites with the published underived
inverse-image compositors. All three coefficient functors and both inverse images are
exact. Apply their termwise functors on complexes and localize at quasi-isomorphisms.
The exact-functor localization comparisons and the published left-derived-to-termwise
isomorphisms give P. Localization carries the underived composition equation to the
displayed equation, because the published total inverse-image compositors are the
localized underived compositors. No direct image is derived in this argument, and no
properness, boundedness or qcqs hypothesis occurs. Empty schemes and the zero ring
use the same constant-section and adjunction identities. -/
theorem finiteCoefficientPullbackEncoding
    (e : Mon.mk R ≅ Mon.mk (coefficient A))
    (E : ∀ T : Scheme.{u}, Encoding A T) :
    ∃ P : Family A R e E,
      ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
        (M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
          (condensedRingObj R Z))),
        (coefficientEncoding A e X (E X)).map
            ((CondensedRing.leftDerivedUpperStarComp R f g).hom.app M) ≫
          (P f).hom.app ((pull R g).obj M) ≫
          (fixedPull A f).map ((P g).hom.app M) =
        (P (f ≫ g)).hom.app M ≫
          (ProEtale.leftDerivedUpperStarComp
            (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f g).hom.app
              ((coefficientEncoding A e Z (E Z)).obj M) := by
  refine ⟨fun {_ _} f ↦ totalPull A R e E f, ?_⟩
  intro X Y Z f g M
  apply edge_comp
    (mapDerivedCategoryTriangleIso (CondensedRing.upperStarComp R f g))
    (mapDerivedCategoryTriangleIso
      (upperStarComp (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f g))
    (CondensedRing.leftDerivedUpperStarComp R f g)
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f g)
    (normalizedPull A R e E (f ≫ g)) (normalizedPull A R e E g)
    (normalizedPull A R e E f)
    (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory R (f ≫ g))
    (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory R g)
    (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory R f)
    (leftDerivedUpperStarIsoMapDerivedCategory
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) (f ≫ g))
    (leftDerivedUpperStarIsoMapDerivedCategory
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) g)
    (leftDerivedUpperStarIsoMapDerivedCategory
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f)
    (internal_compositor R f g) (fixed_compositor A f g) ?_ M
  intro N
  apply vertex_comp
    (mapDerivedCategoryTriangleIso (CondensedRing.upperStarComp R f g))
    (mapDerivedCategoryTriangleIso
      (upperStarComp (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f g))
    (localizedPull A R e E (f ≫ g)) (localizedPull A R e E g)
    (localizedPull A R e E f)
    (heartDerivedIso A R e Z (E Z)) (heartDerivedIso A R e Y (E Y))
    (heartDerivedIso A R e X (E X)) ?_ N
  intro L
  exact derived_comp
    (CondensedRing.upperStar R (f ≫ g)) (CondensedRing.upperStar R g)
    (CondensedRing.upperStar R f)
    (upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) (f ≫ g))
    (upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) g)
    (upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f)
    (heart A R e Z (E Z)) (heart A R e Y (E Y)) (heart A R e X (E X))
    (CondensedRing.upperStarComp R f g)
    (upperStarComp (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f g)
    (heartPull A R e (f ≫ g) (E X) (E Z)) (heartPull A R e g (E Y) (E Z))
    (heartPull A R e f (E X) (E Y))
    (heartPull_comp A R e f g (E X) (E Y) (E Z)) L

end AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary.CoefficientPullback
