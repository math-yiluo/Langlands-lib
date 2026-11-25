/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalDiagonalRightDerived
public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerTraceModels
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.SingleFunctor
import all WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTraceScalarComparisons

/-! # Single-object comparisons and full normalization of the varying square -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
universe a b v z w wc wv
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalTrace

private theorem rightSingle_eq
    {A B : Type a} [Category.{v} A] [Category.{v} B] [Abelian A] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    (F : A ⥤ B) [F.Additive] (RF : DiagonalRightDerived F) (M : A) :
    diagonalTraceRightSingle F RF M =
      DerivedCategory.Q.map ((F.mapCochainComplexSingleFunctor 0).inv.app M) ≫
        RF.η.app ((CochainComplex.singleFunctor A 0).obj M) := by
  simp only [diagonalTraceRightSingle, DerivedCategory.singleFunctorIsoCompQ,
    Iso.refl_hom, Iso.refl_inv, NatTrans.id_app, Category.id_comp]
  erw [RF.R.map_id, Category.comp_id]
  rfl

private theorem rightSingle_naturality
    {A B : Type a} [Category.{v} A] [Category.{v} B] [Abelian A] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    (F : A ⥤ B) [F.Additive] (RF : DiagonalRightDerived F)
    {M N : A} (f : M ⟶ N) :
    (DerivedCategory.singleFunctor B 0).map (F.map f) ≫
        diagonalTraceRightSingle F RF N =
      diagonalTraceRightSingle F RF M ≫
        RF.R.map ((DerivedCategory.singleFunctor A 0).map f) := by
  let t : F ⋙ CochainComplex.singleFunctor B 0 ⋙ DerivedCategory.Q ⟶
      CochainComplex.singleFunctor A 0 ⋙ DerivedCategory.Q ⋙ RF.R :=
    Functor.whiskerRight (F.mapCochainComplexSingleFunctor 0).inv DerivedCategory.Q ≫
      Functor.whiskerLeft (CochainComplex.singleFunctor A 0) RF.η
  simpa only [rightSingle_eq, t, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.comp_map] using! t.naturality f

/-- The degree-zero square for an exact scalar restriction. This named proposition
keeps concrete system-category specializations from expanding the equality repeatedly.
Source: normalized scalar restriction (blueprint:
lem-sfb-diagonal-trace-varying-full-normalization). -/
@[irreducible]
def DiagonalSingleSquare
    {A B C D : Type a} [Category.{v} A] [Category.{v} B]
    [Category.{v} C] [Category.{v} D] [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    [HasDerivedCategory.{wc} C] [HasDerivedCategory.{wc} D]
    (F : A ⥤ B) (G : C ⥤ D) [F.Additive] [G.Additive]
    (U : A ⥤ C) (V : B ⥤ D) [U.Additive] [V.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (RF : DiagonalRightDerived F) (RG : DiagonalRightDerived G)
    (ordinary : F ⋙ V ≅ U ⋙ G)
    (e : RF.R ⋙ V.mapDerivedCategory ≅ U.mapDerivedCategory ⋙ RG.R) (M : A) : Prop :=
    V.mapDerivedCategory.map (diagonalTraceRightSingle F RF M) ≫
        e.hom.app ((DerivedCategory.singleFunctor A 0).obj M) ≫
        RG.R.map ((U.mapDerivedCategorySingleFunctor 0).hom.app M) =
      (V.mapDerivedCategorySingleFunctor 0).hom.app (F.obj M) ≫
        (DerivedCategory.singleFunctor D 0).map (ordinary.hom.app M) ≫
        diagonalTraceRightSingle G RG (U.obj M)

private theorem exactSquare_single
    {A B C D : Type a} [Category.{v} A] [Category.{v} B]
    [Category.{v} C] [Category.{v} D] [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    [HasDerivedCategory.{wc} C] [HasDerivedCategory.{wc} D]
    (F : A ⥤ B) (G : C ⥤ D) [F.Additive] [G.Additive]
    (U : A ⥤ C) (V : B ⥤ D) [U.Additive] [V.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (RF : DiagonalRightDerived F) (RG : DiagonalRightDerived G)
    (ordinary : F ⋙ V ≅ U ⋙ G)
    (e : RF.R ⋙ V.mapDerivedCategory ≅ U.mapDerivedCategory ⋙ RG.R)
    (hn : ∀ P : CochainComplex A ℤ,
      V.mapDerivedCategory.map (RF.η.app P) ≫ e.hom.app (DerivedCategory.Q.obj P) ≫
          RG.R.map (U.mapDerivedCategoryFactors.hom.app P) =
        V.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map
            ((NatTrans.mapHomologicalComplex ordinary.hom (.up ℤ)).app P) ≫
          RG.η.app ((U.mapHomologicalComplex (.up ℤ)).obj P)) (M : A) :
    V.mapDerivedCategory.map (diagonalTraceRightSingle F RF M) ≫
        e.hom.app ((DerivedCategory.singleFunctor A 0).obj M) ≫
        RG.R.map ((U.mapDerivedCategorySingleFunctor 0).hom.app M) =
      (V.mapDerivedCategorySingleFunctor 0).hom.app (F.obj M) ≫
        (DerivedCategory.singleFunctor D 0).map (ordinary.hom.app M) ≫
        diagonalTraceRightSingle G RG (U.obj M) := by
  let P := (CochainComplex.singleFunctor A 0).obj M
  have h := hn P
  rw [rightSingle_eq, rightSingle_eq]
  simp only [Functor.map_comp]
  rw [U.mapDerivedCategorySingleFunctor_hom_app_eq,
    V.mapDerivedCategorySingleFunctor_hom_app_eq]
  simp only [Functor.map_comp, Category.assoc]
  erw [reassoc_of% h]
  have hη := RG.η.naturality ((U.mapCochainComplexSingleFunctor 0).hom.app M)
  dsimp only [Functor.comp_map] at hη
  erw [← hη]
  have hV := V.mapDerivedCategoryFactors.hom.naturality
    ((F.mapCochainComplexSingleFunctor 0).inv.app M)
  dsimp only [Functor.comp_map] at hV
  erw [reassoc_of% hV]
  have hc :
      (V.mapHomologicalComplex (.up ℤ)).map
          ((F.mapCochainComplexSingleFunctor 0).inv.app M) ≫
        (NatTrans.mapHomologicalComplex ordinary.hom (.up ℤ)).app P ≫
        (G.mapHomologicalComplex (.up ℤ)).map
          ((U.mapCochainComplexSingleFunctor 0).hom.app M) =
      (V.mapCochainComplexSingleFunctor 0).hom.app (F.obj M) ≫
        (CochainComplex.singleFunctor D 0).map (ordinary.hom.app M) ≫
        (G.mapCochainComplexSingleFunctor 0).inv.app (U.obj M) := by
    ext i
    by_cases hi : i = 0
    · subst i
      simp [Functor.mapCochainComplexSingleFunctor, CochainComplex.singleFunctor,
        HomologicalComplex.singleObjXSelf,
        HomologicalComplex.singleObjXIsoOfEq, HomologicalComplex.single, P]
    · exact (V.map_isZero
        (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 (F.obj M) i hi)).eq_of_src _ _
  have hc' := congrArg (fun k ↦
    V.mapDerivedCategoryFactors.hom.app ((CochainComplex.singleFunctor B 0).obj (F.obj M)) ≫
      DerivedCategory.Q.map k ≫
        RG.η.app ((CochainComplex.singleFunctor C 0).obj (U.obj M))) hc
  simpa only [Functor.map_comp, Category.assoc] using! hc'

private theorem cochain_unit_normalization
    {A B : Type a} [Category.{v} A] [Category.{v} B] [Abelian A] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    [Abelian.HasKInjectiveResolutions B]
    {L : A ⥤ B} {R : B ⥤ A} [L.Additive] [R.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (a : L ⊣ R) (P : CochainComplex A ℤ) :
    a.mapDerivedCategoryRightDerivedAdjunction.unit.app (DerivedCategory.Q.obj P) ≫
        R.rightDerivedFunctor.map (L.mapDerivedCategoryFactors.hom.app P) =
      DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app P) ≫
        R.rightDerivedFunctorUnitQ ((L.mapHomologicalComplex (.up ℤ)).obj P) := by
  have h := (a.mapHomotopyCategory (.up ℤ)).derivedη_fac_app
    (HomotopyCategory.quasiIso A (.up ℤ)) L.mapDerivedCategoryFactorsh.hom
    R.rightDerivedFunctorUnit ((HomotopyCategory.quotient A (.up ℤ)).obj P)
  change a.mapDerivedCategoryRightDerivedAdjunction.unit.app _ ≫
    R.rightDerivedFunctor.map (L.mapDerivedCategoryFactorsh.hom.app _) = _ at h
  simp only [Functor.rightDerivedFunctorUnitQ, Functor.mapDerivedCategoryFactorsh_hom_app,
    Adjunction.mapHomotopyCategory_unit_app_quotient,
    Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift_inv,
    DerivedCategory.quotientCompQhIso, HomologicalComplexUpToQuasiIso.quotientCompQhIso,
    Functor.map_comp, Quotient.lift.isLift_hom] at h ⊢
  erw [L.mapDerivedCategory.map_id, R.rightDerivedFunctor.map_id,
    DerivedCategory.Qh.map_id, R.rightDerivedFunctor.map_id] at h
  erw [R.rightDerivedFunctor.map_id]
  repeat erw [Category.id_comp]
  repeat erw [Category.comp_id]
  simpa only [Category.id_comp, Category.comp_id] using! h

private theorem adjunct_single
    {A B : Type a} [Category.{v} A] [Category.{v} B] [Abelian A] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    [Abelian.HasKInjectiveResolutions B]
    {L : A ⥤ B} {R : B ⥤ A} [L.Additive] [R.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (a : L ⊣ R) (M : A) (N : B) (f : L.obj M ⟶ N) :
    a.mapDerivedCategoryRightDerivedAdjunction.homEquiv _ _
        ((L.mapDerivedCategorySingleFunctor 0).hom.app M ≫
          (DerivedCategory.singleFunctor B 0).map f) =
      (DerivedCategory.singleFunctor A 0).map (a.homEquiv _ _ f) ≫
        diagonalTraceRightSingle R (canonicalDiagonalRightDerived R) N := by
  let P := (CochainComplex.singleFunctor A 0).obj M
  let t := (L.mapCochainComplexSingleFunctor 0).hom.app M ≫
    (CochainComplex.singleFunctor B 0).map f
  have hc : (a.mapHomologicalComplex (.up ℤ)).unit.app P ≫
      (R.mapHomologicalComplex (.up ℤ)).map t =
    (CochainComplex.singleFunctor A 0).map (a.homEquiv _ _ f) ≫
      (R.mapCochainComplexSingleFunctor 0).inv.app N := by
    ext i
    by_cases hi : i = 0
    · subst i
      simp [P, t, Functor.mapCochainComplexSingleFunctor, CochainComplex.singleFunctor,
        HomologicalComplex.singleObjXSelf,
        HomologicalComplex.singleObjXIsoOfEq, HomologicalComplex.single, Adjunction.homEquiv_unit]
    · exact (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 M i hi).eq_of_src _ _
  have hu := cochain_unit_normalization a P
  have hn := R.rightDerivedFunctorUnitQ_naturality t
  rw [Adjunction.homEquiv_unit, L.mapDerivedCategorySingleFunctor_hom_app_eq]
  rw [rightSingle_eq]
  change _ = (DerivedCategory.singleFunctor A 0).map (a.homEquiv _ _ f) ≫
    DerivedCategory.Q.map ((R.mapCochainComplexSingleFunctor 0).inv.app N) ≫
      R.rightDerivedFunctorUnitQ ((CochainComplex.singleFunctor B 0).obj N)
  calc
    _ = (a.mapDerivedCategoryRightDerivedAdjunction.unit.app (DerivedCategory.Q.obj P) ≫
          R.rightDerivedFunctor.map (L.mapDerivedCategoryFactors.hom.app P)) ≫
        R.rightDerivedFunctor.map (DerivedCategory.Q.map t) := by
      simp only [t, Functor.map_comp, Category.assoc]
      rfl
    _ = DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app P) ≫
        R.rightDerivedFunctorUnitQ ((L.mapHomologicalComplex (.up ℤ)).obj P) ≫
        R.rightDerivedFunctor.map (DerivedCategory.Q.map t) := by rw [hu, Category.assoc]
    _ = DerivedCategory.Q.map
          ((a.mapHomologicalComplex (.up ℤ)).unit.app P ≫
            (R.mapHomologicalComplex (.up ℤ)).map t) ≫
        R.rightDerivedFunctorUnitQ ((CochainComplex.singleFunctor B 0).obj N) := by
      erw [← hn]
      simp only [Functor.map_comp, Category.assoc]
    _ = _ := by
      rw [hc, Functor.map_comp, Category.assoc]
      rfl

private theorem natTrans_ext_kInjective
    {A : Type a} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    [Abelian.HasKInjectiveResolutions A] {D : Type b} [Category.{z} D]
    {F G : DerivedCategory A ⥤ D} (α β : F ⟶ G)
    (h : ∀ I : CochainComplex A ℤ, I.IsKInjective →
      α.app (DerivedCategory.Q.obj I) = β.app (DerivedCategory.Q.obj I)) : α = β := by
  apply NatTrans.ext
  funext M
  obtain ⟨I, hI, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isKInjective M
  apply (cancel_mono (G.map e.hom)).mp
  rw [← α.naturality e.hom, ← β.naturality e.hom, h I hI]

/-- Normalization on K-injective representatives determines the full derived square.

Source: diagonal tower trace proof (1), normalized scalar restriction before the
Milnor step; Stacks Tag 070G, uniqueness of total right derived functors.
(blueprint: lem-sfb-diagonal-trace-varying-full-normalization).

Proof: acyclicity constructs the exact derived square with its full normalization.
On a K-injective complex the cochain unit is the inverse of the canonical computation
isomorphism. Cancelling this unit identifies the constructed comparison with the
supplied comparison there. Every derived object is isomorphic to a K-injective
complex, so naturality identifies the two comparison transformations everywhere.
Substitute this equality into the normalization of the constructed square. -/
theorem diagonalTrace_full_normalization_of_kInjective
    {A B C D : Type a} [Category.{v} A] [Category.{v} B]
    [Category.{v} C] [Category.{v} D] [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    [HasDerivedCategory.{wc} C] [HasDerivedCategory.{wc} D]
    [Abelian.HasKInjectiveResolutions A]
    (F : A ⥤ B) (G : C ⥤ D) [F.Additive] [G.Additive]
    (U : A ⥤ C) (V : B ⥤ D) [U.Additive] [V.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (RG : DiagonalRightDerived G) (ordinary : F ⋙ V ≅ U ⋙ G)
    (e : F.rightDerivedFunctor ⋙ V.mapDerivedCategory ≅ U.mapDerivedCategory ⋙ RG.R)
    (hacyc : ∀ (I : CochainComplex A ℤ), I.IsKInjective →
      IsIso (RG.η.app ((U.mapHomologicalComplex (.up ℤ)).obj I)))
    (hk : ∀ (I : CochainComplex A ℤ) (hI : I.IsKInjective),
      letI := hI
      e.hom.app (DerivedCategory.Q.obj I) ≫
          RG.R.map (U.mapDerivedCategoryFactors.hom.app I) =
        V.mapDerivedCategory.map (F.rightDerivedFunctorObjQIso I).hom ≫
          V.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj I) ≫
          DerivedCategory.Q.map
            ((NatTrans.mapHomologicalComplex ordinary.hom (.up ℤ)).app I) ≫
          RG.η.app ((U.mapHomologicalComplex (.up ℤ)).obj I))
    (P : CochainComplex A ℤ) :
    V.mapDerivedCategory.map (F.rightDerivedFunctorUnitQ P) ≫
        e.hom.app (DerivedCategory.Q.obj P) ≫
        RG.R.map (U.mapDerivedCategoryFactors.hom.app P) =
      V.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex ordinary.hom (.up ℤ)).app P) ≫
        RG.η.app ((U.mapHomologicalComplex (.up ℤ)).obj P) := by
  let s := squareOfAcyclic F G U V (canonicalDiagonalRightDerived F) RG ordinary hacyc
  have hs (I : CochainComplex A ℤ) [I.IsKInjective] :
      s.iso.hom.app (DerivedCategory.Q.obj I) = e.hom.app (DerivedCategory.Q.obj I) := by
    apply (cancel_mono (RG.R.map (U.mapDerivedCategoryFactors.hom.app I))).mp
    have h := s.normalization I
    change V.mapDerivedCategory.map (F.rightDerivedFunctorUnitQ I) ≫ _ = _ at h
    rw [Functor.rightDerivedFunctorUnitQ_eq] at h
    have h' := congrArg
      (fun k ↦ V.mapDerivedCategory.map (F.rightDerivedFunctorObjQIso I).hom ≫ k) h
    simp only [← Category.assoc, ← Functor.map_comp, Iso.hom_inv_id] at h'
    simp only [CategoryTheory.Functor.map_id, Category.id_comp] at h'
    exact h'.trans (by simpa only [Category.assoc] using (hk I inferInstance).symm)
  have he : s.iso.hom = e.hom :=
    natTrans_ext_kInjective _ _ (fun I hI ↦ by let := hI; exact hs I)
  rw [← he]
  exact s.normalization P

private theorem exactSquare_single_of_kInjective
    {A B C D : Type a} [Category.{v} A] [Category.{v} B]
    [Category.{v} C] [Category.{v} D] [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    [HasDerivedCategory.{wc} C] [HasDerivedCategory.{wc} D]
    [Abelian.HasKInjectiveResolutions A]
    (F : A ⥤ B) (G : C ⥤ D) [F.Additive] [G.Additive]
    (U : A ⥤ C) (V : B ⥤ D) [U.Additive] [V.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (RG : DiagonalRightDerived G) (ordinary : F ⋙ V ≅ U ⋙ G)
    (e : F.rightDerivedFunctor ⋙ V.mapDerivedCategory ≅ U.mapDerivedCategory ⋙ RG.R)
    (hacyc : ∀ (I : CochainComplex A ℤ), I.IsKInjective →
      IsIso (RG.η.app ((U.mapHomologicalComplex (.up ℤ)).obj I)))
    (hk : ∀ (I : CochainComplex A ℤ) (hI : I.IsKInjective),
      letI := hI
      e.hom.app (DerivedCategory.Q.obj I) ≫
          RG.R.map (U.mapDerivedCategoryFactors.hom.app I) =
        V.mapDerivedCategory.map (F.rightDerivedFunctorObjQIso I).hom ≫
          V.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj I) ≫
          DerivedCategory.Q.map
            ((NatTrans.mapHomologicalComplex ordinary.hom (.up ℤ)).app I) ≫
          RG.η.app ((U.mapHomologicalComplex (.up ℤ)).obj I))
    (M : A) :
    DiagonalSingleSquare F G U V (canonicalDiagonalRightDerived F) RG ordinary e M := by
  unfold DiagonalSingleSquare
  exact exactSquare_single F G U V (canonicalDiagonalRightDerived F) RG ordinary e
    (diagonalTrace_full_normalization_of_kInjective F G U V RG ordinary e hacyc hk) M

private theorem limitSquare_single
    {A B : Type (a + 1)} [Category.{a} A] [Category.{a} B] [Abelian A] [Abelian B]
    [HasLimitsOfShape ℕᵒᵖ A] [HasLimitsOfShape ℕᵒᵖ B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)]
    (F : A ⥤ B) [F.Additive]
    (LX : DiagonalRlim A) (LS : DiagonalRlim B)
    (Rf : DiagonalRightDerived F)
    (Rt : DiagonalRightDerived ((Functor.whiskeringRight ℕᵒᵖ A B).obj F))
    (o : (lim : (ℕᵒᵖ ⥤ A) ⥤ A) ⋙ F ≅
      (Functor.whiskeringRight ℕᵒᵖ A B).obj F ⋙ lim)
    (e : LX.R ⋙ Rf.R ≅ Rt.R ⋙ LS.R)
    (hn : ∀ P : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
      Rf.η.app (((lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (.up ℤ)).obj P) ≫
          Rf.R.map (LX.η.app P) ≫ e.hom.app (DerivedCategory.Q.obj P) =
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex o.hom (.up ℤ)).app P) ≫
          LS.η.app ((((Functor.whiskeringRight ℕᵒᵖ A B).obj F).mapHomologicalComplex
            (.up ℤ)).obj P) ≫ LS.R.map (Rt.η.app P)) (H : ℕᵒᵖ ⥤ A) :
    diagonalTraceRightSingle F Rf (limit H) ≫
        Rf.R.map (diagonalOrdinaryRlim LX H) ≫
        e.hom.app ((DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ A) 0).obj H) =
      (DerivedCategory.singleFunctor B 0).map (o.hom.app H) ≫
        diagonalOrdinaryRlim LS (H ⋙ F) ≫
        LS.R.map (diagonalTraceRightSingle
          ((Functor.whiskeringRight ℕᵒᵖ A B).obj F) Rt H) := by
  let FT := (Functor.whiskeringRight ℕᵒᵖ A B).obj F
  let P := (CochainComplex.singleFunctor (ℕᵒᵖ ⥤ A) 0).obj H
  have hlimX : diagonalOrdinaryRlim LX H =
      diagonalTraceRightSingle (lim : (ℕᵒᵖ ⥤ A) ⥤ A) LX.toDiagonalRightDerived H := rfl
  have hlimS : diagonalOrdinaryRlim LS (H ⋙ F) =
      diagonalTraceRightSingle (lim : (ℕᵒᵖ ⥤ B) ⥤ B) LS.toDiagonalRightDerived
        (H ⋙ F) := rfl
  rw [hlimX, hlimS, rightSingle_eq, rightSingle_eq, rightSingle_eq, rightSingle_eq]
  simp only [Functor.map_comp, Category.assoc]
  have hf := Rf.η.naturality
    (((lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapCochainComplexSingleFunctor 0).inv.app H)
  have hs := LS.η.naturality ((FT.mapCochainComplexSingleFunctor 0).inv.app H)
  dsimp only [Functor.comp_map] at hf hs
  erw [← reassoc_of% hf, hn P, ← reassoc_of% hs]
  have hA : limMap (𝟙 H) = 𝟙 (limit H) :=
    (lim : (ℕᵒᵖ ⥤ A) ⥤ A).map_id H
  have hB : limMap (𝟙 (H ⋙ F)) = 𝟙 (limit (H ⋙ F)) :=
    (lim : (ℕᵒᵖ ⥤ B) ⥤ B).map_id (H ⋙ F)
  have hc :
      (F.mapCochainComplexSingleFunctor 0).inv.app (limit H) ≫
        (F.mapHomologicalComplex (.up ℤ)).map
          (((lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapCochainComplexSingleFunctor 0).inv.app H) ≫
        (NatTrans.mapHomologicalComplex o.hom (.up ℤ)).app P =
      (CochainComplex.singleFunctor B 0).map (o.hom.app H) ≫
        ((lim : (ℕᵒᵖ ⥤ B) ⥤ B).mapCochainComplexSingleFunctor 0).inv.app (H ⋙ F) ≫
        ((lim : (ℕᵒᵖ ⥤ B) ⥤ B).mapHomologicalComplex (.up ℤ)).map
          ((FT.mapCochainComplexSingleFunctor 0).inv.app H) := by
    ext i
    by_cases hi : i = 0
    · subst i
      simp [Functor.mapCochainComplexSingleFunctor, CochainComplex.singleFunctor,
        HomologicalComplex.singleObjXSelf,
        HomologicalComplex.singleObjXIsoOfEq, HomologicalComplex.single, P, FT, hA, hB]
    · exact (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 (F.obj (limit H))
        i hi).eq_of_src _ _
  have hc' := congrArg (fun k ↦ DerivedCategory.Q.map k ≫
    LS.η.app ((FT.mapHomologicalComplex (.up ℤ)).obj P) ≫
      LS.R.map (Rt.η.app P)) hc
  simpa only [Functor.map_comp, Category.assoc] using! hc'

/-- Compatibility of a varying derived arrow with the single-object scalar comparisons.
Source: coefficient unit square (blueprint:
lem-sfb-diagonal-trace-varying-full-normalization). -/
@[irreducible]
def DiagonalSingleUnitCompatible
    {VX VS TX TS : Type a} [Category.{v} VX] [Category.{v} VS]
    [Category.{v} TX] [Category.{v} TS]
    [Abelian VX] [Abelian VS] [Abelian TX] [Abelian TS]
    [HasDerivedCategory.{w} VX] [HasDerivedCategory.{w} VS]
    [HasDerivedCategory.{wc} TX] [HasDerivedCategory.{wc} TS]
    (G : TX ⥤ TS) [G.Additive]
    (U : VX ⥤ TX) (V : VS ⥤ TS) [U.Additive] [V.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (RG : DiagonalRightDerived G) (RV : DerivedCategory VX ⥤ DerivedCategory VS)
    (e : RV ⋙ V.mapDerivedCategory ≅ U.mapDerivedCategory ⋙ RG.R)
    (NX : VX) (NS : VS)
    (δ : (DerivedCategory.singleFunctor VS 0).obj NS ⟶
      RV.obj ((DerivedCategory.singleFunctor VX 0).obj NX))
    (β : V.obj NS ⟶ G.obj (U.obj NX)) : Prop :=
  V.mapDerivedCategory.map δ ≫
      e.hom.app ((DerivedCategory.singleFunctor VX 0).obj NX) =
    (V.mapDerivedCategorySingleFunctor 0).hom.app NS ≫
      (DerivedCategory.singleFunctor TS 0).map β ≫
      diagonalTraceRightSingle G RG (U.obj NX) ≫
      RG.R.map ((U.mapDerivedCategorySingleFunctor 0).inv.app NX)

private theorem singleUnitCompatible_of_singleSquare
    {A B C D : Type a} [Category.{v} A] [Category.{v} B]
    [Category.{v} C] [Category.{v} D] [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    [HasDerivedCategory.{wc} C] [HasDerivedCategory.{wc} D]
    (F : A ⥤ B) (G : C ⥤ D) [F.Additive] [G.Additive]
    (U : A ⥤ C) (V : B ⥤ D) [U.Additive] [V.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (RF : DiagonalRightDerived F) (RG : DiagonalRightDerived G)
    (ordinary : F ⋙ V ≅ U ⋙ G)
    (e : RF.R ⋙ V.mapDerivedCategory ≅ U.mapDerivedCategory ⋙ RG.R)
    (NX : A) (NS : B) (b : NS ⟶ F.obj NX)
    (δ : (DerivedCategory.singleFunctor B 0).obj NS ⟶
      RF.R.obj ((DerivedCategory.singleFunctor A 0).obj NX))
    (hs : DiagonalSingleSquare F G U V RF RG ordinary e NX)
    (ha : δ = (DerivedCategory.singleFunctor B 0).map b ≫
      diagonalTraceRightSingle F RF NX) :
    DiagonalSingleUnitCompatible G U V RG RF.R e NX NS δ
      (V.map b ≫ ordinary.hom.app NX) := by
  unfold DiagonalSingleUnitCompatible
  unfold DiagonalSingleSquare at hs
  apply (cancel_mono (RG.R.map ((U.mapDerivedCategorySingleFunctor 0).hom.app NX))).mp
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
  rw [ha, Functor.map_comp, Category.assoc, hs]
  erw [(V.mapDerivedCategorySingleFunctor 0).hom.naturality_assoc b]
  simp only [Functor.comp_map, Functor.map_comp, Category.assoc]
  erw [RG.R.map_id, Category.comp_id]

/-- The definition equation for a completed pushforward unit, recorded without expanding
its derived comparison at concrete coefficient rings.
Source: completed coefficient unit (blueprint:
lem-sfb-diagonal-trace-varying-full-normalization). -/
@[irreducible]
def DiagonalFinitePushUnitFormula
    {CX CS A B : Type (a + 1)}
    [Category.{a} CX] [Category.{a} CS] [Category.{a} A] [Category.{a} B]
    [Abelian CX] [Abelian CS] [Abelian A] [Abelian B]
    [HasDerivedCategory.{w} CX] [HasDerivedCategory.{w} CS]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    (FC : CX ⥤ CS) (F : A ⥤ B) [FC.Additive] [F.Additive]
    (U : CX ⥤ A) (V : CS ⥤ B) [U.Additive] [V.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (Rc : DiagonalRightDerived FC) (Rf : DiagonalRightDerived F)
    (e : Rc.R ⋙ V.mapDerivedCategory ≅ U.mapDerivedCategory ⋙ Rf.R)
    (MX : CX) (MS : CS) (b : MS ⟶ FC.obj MX)
    (d : V.mapDerivedCategory.obj ((DerivedCategory.singleFunctor CS 0).obj MS) ⟶
      Rf.R.obj (U.mapDerivedCategory.obj ((DerivedCategory.singleFunctor CX 0).obj MX))) :
    Prop :=
  d = V.mapDerivedCategory.map
      ((DerivedCategory.singleFunctor CS 0).map b ≫ diagonalTraceRightSingle FC Rc MX) ≫
    e.hom.app ((DerivedCategory.singleFunctor CX 0).obj MX)

/-- The exact scalar cone's definition equation, with its derived maps kept in a named
proposition until it is used in a generic diagram calculation.
Source: coefficient cone comparison (blueprint:
lem-sfb-diagonal-trace-varying-full-normalization). -/
@[irreducible]
def DiagonalExactConeFormula
    {CX VX A : Type (a + 1)} [Category.{a} CX] [Category.{a} VX] [Category.{a} A]
    [Abelian CX] [Abelian VX] [Abelian A] [HasLimitsOfShape ℕᵒᵖ A]
    [HasDerivedCategory.{wc} CX] [HasDerivedCategory.{wv} VX]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)]
    (U : CX ⥤ A) (V : VX ⥤ (ℕᵒᵖ ⥤ A)) [U.Additive] [V.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (L : DiagonalRlim A) (M : CX) (N : VX) (cx : U.obj M ⟶ limit (V.obj N))
    (d : U.mapDerivedCategory.obj ((DerivedCategory.singleFunctor CX 0).obj M) ⟶
      L.R.obj (V.mapDerivedCategory.obj ((DerivedCategory.singleFunctor VX 0).obj N))) :
    Prop :=
  d = (U.mapDerivedCategorySingleFunctor 0).hom.app M ≫
    (DerivedCategory.singleFunctor A 0).map cx ≫ diagonalOrdinaryRlim L (V.obj N) ≫
    L.R.map ((V.mapDerivedCategorySingleFunctor 0).inv.app N)

private theorem exactConeComparison_formula
    {CX VX A : Type (a + 1)} [Category.{a} CX] [Category.{a} VX] [Category.{a} A]
    [Abelian CX] [Abelian VX] [Abelian A] [HasLimitsOfShape ℕᵒᵖ A]
    [HasDerivedCategory.{wc} CX] [HasDerivedCategory.{wv} VX]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)]
    (U : CX ⥤ A) (V : VX ⥤ (ℕᵒᵖ ⥤ A)) [U.Additive] [V.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (L : DiagonalRlim A) (M : CX) (N : VX)
    (π : (Functor.const ℕᵒᵖ).obj (U.obj M) ⟶ V.obj N) :
    DiagonalExactConeFormula U V L M N (limit.lift (V.obj N) ⟨U.obj M, π⟩)
      (exactConeComparison U V L M N π) := by
  unfold DiagonalExactConeFormula exactConeComparison
  rfl

private theorem common_unit_diagram
    {CX CS VX VS A B : Type (a + 1)}
    [Category.{a} CX] [Category.{a} CS] [Category.{a} VX] [Category.{a} VS]
    [Category.{a} A] [Category.{a} B]
    [Abelian CX] [Abelian CS] [Abelian VX] [Abelian VS] [Abelian A] [Abelian B]
    [HasLimitsOfShape ℕᵒᵖ A] [HasLimitsOfShape ℕᵒᵖ B]
    [HasDerivedCategory.{w} CX] [HasDerivedCategory.{w} CS]
    [HasDerivedCategory.{wv} VX] [HasDerivedCategory.{wv} VS]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)]
    (FC : CX ⥤ CS) (F : A ⥤ B) [FC.Additive] [F.Additive]
    (UC : CX ⥤ A) (VC : CS ⥤ B) [UC.Additive] [VC.Additive]
    [PreservesFiniteLimits UC] [PreservesFiniteColimits UC]
    [PreservesFiniteLimits VC] [PreservesFiniteColimits VC]
    (U : VX ⥤ (ℕᵒᵖ ⥤ A)) (V : VS ⥤ (ℕᵒᵖ ⥤ B)) [U.Additive] [V.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (Rc : DiagonalRightDerived FC) (Rf : DiagonalRightDerived F)
    (Rt : DiagonalRightDerived ((Functor.whiskeringRight ℕᵒᵖ A B).obj F))
    (LX : DiagonalRlim A) (LS : DiagonalRlim B)
    (oC : FC ⋙ VC ≅ UC ⋙ F) (c : ExactSquare FC F UC VC Rc Rf oC)
    (oL : (lim : (ℕᵒᵖ ⥤ A) ⥤ A) ⋙ F ≅
      (Functor.whiskeringRight ℕᵒᵖ A B).obj F ⋙ lim)
    (eL : LX.R ⋙ Rf.R ≅ Rt.R ⋙ LS.R)
    (hnL : ∀ P : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
      Rf.η.app (((lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (.up ℤ)).obj P) ≫
          Rf.R.map (LX.η.app P) ≫ eL.hom.app (DerivedCategory.Q.obj P) =
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex oL.hom (.up ℤ)).app P) ≫
          LS.η.app ((((Functor.whiskeringRight ℕᵒᵖ A B).obj F).mapHomologicalComplex
            (.up ℤ)).obj P) ≫ LS.R.map (Rt.η.app P))
    (RV : DerivedCategory VX ⥤ DerivedCategory VS)
    (eV : RV ⋙ V.mapDerivedCategory ≅ U.mapDerivedCategory ⋙ Rt.R)
    (MX : CX) (MS : CS) (NX : VX) (NS : VS) (b : MS ⟶ FC.obj MX)
    (δ : (DerivedCategory.singleFunctor VS 0).obj NS ⟶
      RV.obj ((DerivedCategory.singleFunctor VX 0).obj NX))
    (cx : UC.obj MX ⟶ limit (U.obj NX)) (cs : VC.obj MS ⟶ limit (V.obj NS))
    (β : V.obj NS ⟶ U.obj NX ⋙ F)
    (ho : VC.map b ≫ oC.hom.app MX ≫ F.map cx ≫ oL.hom.app (U.obj NX) =
      cs ≫ (lim : (ℕᵒᵖ ⥤ B) ⥤ B).map β)
    (hv : DiagonalSingleUnitCompatible
      ((Functor.whiskeringRight ℕᵒᵖ A B).obj F) U V Rt RV eV NX NS δ β)
    (dB : VC.mapDerivedCategory.obj ((DerivedCategory.singleFunctor CS 0).obj MS) ⟶
      Rf.R.obj (UC.mapDerivedCategory.obj ((DerivedCategory.singleFunctor CX 0).obj MX)))
    (dX : UC.mapDerivedCategory.obj ((DerivedCategory.singleFunctor CX 0).obj MX) ⟶
      LX.R.obj (U.mapDerivedCategory.obj ((DerivedCategory.singleFunctor VX 0).obj NX)))
    (dS : VC.mapDerivedCategory.obj ((DerivedCategory.singleFunctor CS 0).obj MS) ⟶
      LS.R.obj (V.mapDerivedCategory.obj ((DerivedCategory.singleFunctor VS 0).obj NS)))
    (hdB : DiagonalFinitePushUnitFormula FC F UC VC Rc Rf c.iso MX MS b dB)
    (hdX : DiagonalExactConeFormula UC U LX MX NX cx dX)
    (hdS : DiagonalExactConeFormula VC V LS MS NS cs dS) :
    ((dB ≫ Rf.R.map dX) ≫
        eL.hom.app (U.mapDerivedCategory.obj ((DerivedCategory.singleFunctor VX 0).obj NX))) ≫
        LS.R.map (eV.inv.app ((DerivedCategory.singleFunctor VX 0).obj NX)) =
      dS ≫ LS.R.map (V.mapDerivedCategory.map δ) := by
  unfold DiagonalFinitePushUnitFormula at hdB
  unfold DiagonalExactConeFormula at hdX hdS
  rw [hdB, hdX, hdS]
  unfold DiagonalSingleUnitCompatible at hv
  have hc := exactSquare_single FC F UC VC Rc Rf oC c.iso c.normalization MX
  have hl := limitSquare_single F LX LS Rf Rt oL eL hnL (U.obj NX)
  have ho' := congrArg ((DerivedCategory.singleFunctor B 0).map) ho
  simp only [Functor.map_comp] at ho'
  have hv' := congrArg (fun k ↦
    (V.mapDerivedCategorySingleFunctor 0).inv.app NS ≫ k ≫
      eV.inv.app ((DerivedCategory.singleFunctor VX 0).obj NX)) hv
  simp only [Category.assoc, Iso.hom_inv_id_app,
    Iso.inv_hom_id_app_assoc] at hv'
  have hvmap := congrArg LS.R.map hv'
  simp only [Functor.map_comp] at hvmap
  simp only [Functor.map_comp, Category.assoc]
  erw [eL.hom.naturality_assoc ((U.mapDerivedCategorySingleFunctor 0).inv.app NX)]
  erw [reassoc_of% hc]
  have hn := (VC.mapDerivedCategorySingleFunctor 0).hom.naturality b
  dsimp only [Functor.comp_map] at hn
  erw [reassoc_of% hn]
  erw [← reassoc_of% rightSingle_naturality F Rf cx]
  erw [reassoc_of% hl]
  erw [reassoc_of% ho']
  have hlim := rightSingle_naturality (lim : (ℕᵒᵖ ⥤ B) ⥤ B) LS.toDiagonalRightDerived β
  change (DerivedCategory.singleFunctor B 0).map ((lim : (ℕᵒᵖ ⥤ B) ⥤ B).map β) ≫
      diagonalOrdinaryRlim LS (U.obj NX ⋙ F) =
    diagonalOrdinaryRlim LS (V.obj NS) ≫
      LS.R.map ((DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ B) 0).map β) at hlim
  erw [reassoc_of% hlim]
  erw [← hvmap]
  erw [LS.R.map_id, Category.comp_id]

end AlgebraicGeometry.ProEtale.DiagonalTrace
