/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedMayerVietorisTriangle
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.AlgebraicGeometry.DerivedMayerVietorisCanonicalData
import WeilConjectures.AlgebraicGeometry.DerivedMayerVietorisDirectImageSquares
import WeilConjectures.AlgebraicGeometry.DerivedMayerVietorisDirectImageBoundary
import WeilConjectures.AlgebraicGeometry.KInjectiveMayerVietorisExact
import WeilConjectures.AlgebraicGeometry.OpenImageComplexComparisonUnit
import WeilConjectures.AlgebraicGeometry.OpenImageComplexComparisonRestriction
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective

/-! # Functoriality of derived Mayer--Vietoris triangles

Source: Stacks Project, Cohomology, Tags 08BV and 0D5T; Derived Categories of Schemes,
Tag 0DJ9 (blueprint: lem-pc-derived-mayer-vietoris-functorial).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits TopologicalSpace Pretriangulated

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048

noncomputable section
namespace AlgebraicGeometry

attribute [local instance 2000] schemeMVModuleAbelian schemeMVDirectImageTriangulated
attribute [local irreducible] schemeMVOpenComparison schemeMVMiddleComparison
  schemeMVOpenRestrictionComparison schemeMVDirectImageComposition

private theorem derived_map_surjective
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    (I J : CochainComplex A ℤ) [J.IsKInjective]
    (φ : DerivedCategory.Q.obj I ⟶ DerivedCategory.Q.obj J) :
    ∃ f : I ⟶ J, DerivedCategory.Q.map f = φ := by
  let e := DerivedCategory.quotientCompQhIso A
  obtain ⟨g, hg⟩ := (CochainComplex.IsKInjective.Qh_map_bijective
    ((HomotopyCategory.quotient _ _).obj I) J).surjective
      (e.hom.app I ≫ φ ≫ e.inv.app J)
  obtain ⟨f, hf⟩ := (HomotopyCategory.quotient A (.up ℤ)).map_surjective g
  refine ⟨f, ?_⟩
  have h := e.hom.naturality f
  dsimp only [Functor.comp_map] at h
  rw [hf, hg] at h
  apply (cancel_epi (e.hom.app I)).mp
  simpa only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id] using h.symm

private theorem computation_naturality
    {A B : Type*} [Category A] [Abelian A] [Category B] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [CategoryTheory.Abelian.HasKInjectiveResolutions A]
    (F : A ⥤ B) [F.Additive]
    (I J : CochainComplex A ℤ) [I.IsKInjective] [J.IsKInjective] (f : I ⟶ J) :
    DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map f) ≫
        (F.rightDerivedFunctorObjQIso J).inv =
      (F.rightDerivedFunctorObjQIso I).inv ≫
        F.rightDerivedFunctor.map (DerivedCategory.Q.map f) := by
  dsimp only [Functor.rightDerivedFunctorObjQIso, Iso.trans_inv, Iso.symm_inv,
    Functor.mapIso_inv, Iso.app_inv, asIso_hom]
  simp only [Category.assoc]
  rw [DerivedCategory.quotientCompQhIso_inv_naturality_assoc]
  have hn := F.rightDerivedFunctorUnit.naturality
    ((HomotopyCategory.quotient A (.up ℤ)).map f)
  change DerivedCategory.Qh.map
      ((HomotopyCategory.quotient B (.up ℤ)).map
        ((F.mapHomologicalComplex (.up ℤ)).map f)) ≫
      F.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient A (.up ℤ)).obj J) =
    F.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient A (.up ℤ)).obj I) ≫
      F.rightDerivedFunctor.map
        (DerivedCategory.Qh.map ((HomotopyCategory.quotient A (.up ℤ)).map f)) at hn
  rw [reassoc_of% hn]
  rw [← F.rightDerivedFunctor.map_comp, ← F.rightDerivedFunctor.map_comp]
  simp only [Iso.app_hom]
  rw [DerivedCategory.quotientCompQhIso_hom_naturality]

private theorem open_comparison_naturality (X : Scheme.{u}) (U : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    (I J : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    [I.IsKInjective] [J.IsKInjective] (f : I ⟶ J)
    (adj : (schemeOpenRestriction X U).mapDerivedCategory ⊣ schemeDerivedDirectImage U.ι) :
    DerivedCategory.Q.map ((schemeOpenModuleImage X U).mapHomologicalComplex (.up ℤ) |>.map f) ≫
        (schemeOpenModuleImageComplexComparison X U J adj).hom =
      (schemeOpenModuleImageComplexComparison X U I adj).hom ≫
        (schemeDerivedDirectImage U.ι).map
          ((schemeOpenRestriction X U).mapDerivedCategory.map (DerivedCategory.Q.map f)) := by
  let L := schemeOpenRestriction X U
  let R := RingedSpace.moduleDirectImage U.ι.toLRSHom.toShHom
  have := isKInjective_schemeOpenRestriction X U I
  have := isKInjective_schemeOpenRestriction X U J
  dsimp only [schemeOpenModuleImageComplexComparison, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Iso.app_hom]
  simp only [Category.assoc]
  have hn := computation_naturality R _ _ ((L.mapHomologicalComplex (.up ℤ)).map f)
  have hh := reassoc_of% hn
  erw [hh]
  erw [← R.rightDerivedFunctor.map_comp_assoc]
  erw [L.mapDerivedCategoryFactors.inv.naturality]
  rw [R.rightDerivedFunctor.map_comp, Category.assoc]
  apply congrArg (fun k => (R.rightDerivedFunctorObjQIso
    ((L.mapHomologicalComplex (.up ℤ)).obj I)).inv ≫
      R.rightDerivedFunctor.map (L.mapDerivedCategoryFactors.inv.app I) ≫ k)
  let a : L ⊣ R := schemeOpenModuleAdjunction X U
  exact (a.mapDerivedCategoryRightDerivedAdjunction.rightAdjointUniq adj).hom.naturality
    (L.mapDerivedCategory.map (DerivedCategory.Q.map f))

private theorem concrete_map (X : Scheme.{u}) (U V : X.Opens)
    (I J : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (f : I ⟶ J) :
    ∃ m : schemeMayerVietorisComplex X U V I ⟶ schemeMayerVietorisComplex X U V J,
      m.τ₁ = f ∧
      m.τ₃ = ((schemeOpenModuleImage X (U ⊓ V)).mapHomologicalComplex (.up ℤ)).map f := by
  let gU := ((schemeOpenModuleImage X U).mapHomologicalComplex (.up ℤ)).map f
  let gV := ((schemeOpenModuleImage X V).mapHomologicalComplex (.up ℤ)).map f
  let gW := ((schemeOpenModuleImage X (U ⊓ V)).mapHomologicalComplex (.up ℤ)).map f
  have hu (W : X.Opens) :
      f ≫ schemeOpenModuleImageComplexUnit X W J =
        schemeOpenModuleImageComplexUnit X W I ≫
          ((schemeOpenModuleImage X W).mapHomologicalComplex (.up ℤ)).map f := by
    apply HomologicalComplex.Hom.ext
    funext n
    exact (schemeOpenModuleAdjunction X W).unit.naturality (f.f n)
  have hr {W A : X.Opens} (i : W ⟶ A) :
      ((schemeOpenModuleImage X A).mapHomologicalComplex (.up ℤ)).map f ≫
          schemeOpenModuleImageComplexRestriction X i J =
        schemeOpenModuleImageComplexRestriction X i I ≫
          ((schemeOpenModuleImage X W).mapHomologicalComplex (.up ℤ)).map f :=
    ((schemeOpenModuleImageRestriction X i).mapHomologicalComplex (.up ℤ)).naturality f
  refine ⟨⟨f, biprod.map gU gV, gW, ?_, ?_⟩, rfl, rfl⟩
  · change f ≫ schemeMayerVietorisF X U V J =
      schemeMayerVietorisF X U V I ≫ biprod.map gU gV
    apply biprod.hom_ext
    · simpa only [schemeMayerVietorisF, Category.assoc, biprod.map_fst,
        biprod.lift_fst_assoc, biprod.lift_fst] using hu U
    · simpa only [schemeMayerVietorisF, Category.assoc, biprod.map_snd,
        biprod.lift_snd_assoc, biprod.lift_snd] using hu V
  · change biprod.map gU gV ≫ schemeMayerVietorisG X U V J =
      schemeMayerVietorisG X U V I ≫ gW
    apply biprod.hom_ext'
    · simpa only [schemeMayerVietorisG, Category.assoc, biprod.inl_map_assoc,
        biprod.inl_desc_assoc, biprod.inl_desc, gU, gW] using hr (homOfLE (inf_le_left : U ⊓ V ≤ U))
    · simpa only [schemeMayerVietorisG, Category.assoc, biprod.inr_map_assoc,
        biprod.inr_desc_assoc, biprod.inr_desc, Preadditive.comp_neg,
        Preadditive.neg_comp, gV, gW] using
        congrArg Neg.neg (hr (homOfLE (inf_le_right : U ⊓ V ≤ V)))

private theorem mv_comm₁ (X : Scheme.{u}) (U V : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))]
    (adjU : (schemeOpenRestriction X U).mapDerivedCategory ⊣ schemeDerivedDirectImage U.ι)
    (adjV : (schemeOpenRestriction X V).mapDerivedCategory ⊣ schemeDerivedDirectImage V.ι)
    {E F : schemeDerivedCategory X} (f : E ⟶ F) :
    biprod.lift (adjU.unit.app E) (adjV.unit.app E) ≫
        biprod.map ((schemeDerivedDirectImage U.ι).map
          ((schemeOpenRestriction X U).mapDerivedCategory.map f))
          ((schemeDerivedDirectImage V.ι).map
            ((schemeOpenRestriction X V).mapDerivedCategory.map f)) =
      f ≫ biprod.lift (adjU.unit.app F) (adjV.unit.app F) := by
  apply biprod.hom_ext
  · simp only [Category.assoc, biprod.map_fst, biprod.lift_fst_assoc]
    erw [biprod.lift_fst]
    simpa only [Functor.id_map, Functor.comp_map] using (adjU.unit.naturality f).symm
  · simp only [Category.assoc, biprod.map_snd, biprod.lift_snd_assoc]
    erw [biprod.lift_snd]
    simpa only [Functor.id_map, Functor.comp_map] using (adjV.unit.naturality f).symm

private theorem mv_comm₂ (X : Scheme.{u}) (U V : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (U ⊓ V).toScheme.toRingedSpace))]
    (adjU : (schemeOpenRestriction X U).mapDerivedCategory ⊣ schemeDerivedDirectImage U.ι)
    (adjV : (schemeOpenRestriction X V).mapDerivedCategory ⊣ schemeDerivedDirectImage V.ι)
    (adjW : (schemeOpenRestriction X (U ⊓ V)).mapDerivedCategory ⊣
      schemeDerivedDirectImage (U ⊓ V).ι)
    {E F : schemeDerivedCategory X} (f : E ⟶ F) :
    biprod.desc
        (schemeDerivedOpenDirectImageRestriction X (homOfLE (inf_le_left : U ⊓ V ≤ U)) adjU adjW E)
        (-(schemeDerivedOpenDirectImageRestriction X
          (homOfLE (inf_le_right : U ⊓ V ≤ V)) adjV adjW E)) ≫
      (schemeDerivedDirectImage (U ⊓ V).ι).map
        ((schemeOpenRestriction X (U ⊓ V)).mapDerivedCategory.map f) =
    biprod.map ((schemeDerivedDirectImage U.ι).map
          ((schemeOpenRestriction X U).mapDerivedCategory.map f))
          ((schemeDerivedDirectImage V.ι).map
            ((schemeOpenRestriction X V).mapDerivedCategory.map f)) ≫
      biprod.desc
        (schemeDerivedOpenDirectImageRestriction X (homOfLE (inf_le_left : U ⊓ V ≤ U)) adjU adjW F)
        (-(schemeDerivedOpenDirectImageRestriction X
          (homOfLE (inf_le_right : U ⊓ V ≤ V)) adjV adjW F)) := by
  let ρ {A : X.Opens}
      [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings A.toScheme.toRingedSpace))]
      (i : U ⊓ V ⟶ A)
      (adjA : (schemeOpenRestriction X A).mapDerivedCategory ⊣
        schemeDerivedDirectImage A.ι) :
      (schemeOpenRestriction X A).mapDerivedCategory ⋙ schemeDerivedDirectImage A.ι ⟶
        (schemeOpenRestriction X (U ⊓ V)).mapDerivedCategory ⋙
          schemeDerivedDirectImage (U ⊓ V).ι :=
    Functor.whiskerLeft
      ((schemeOpenRestriction X A).mapDerivedCategory ⋙ schemeDerivedDirectImage A.ι)
      adjW.unit ≫
      Functor.whiskerRight
        (Functor.whiskerLeft
            ((schemeOpenRestriction X A).mapDerivedCategory ⋙ schemeDerivedDirectImage A.ι)
            (schemeDerivedOpenRestrictionCompIso X i).inv ≫
          Functor.whiskerRight
            (Functor.whiskerLeft (schemeOpenRestriction X A).mapDerivedCategory adjA.counit)
            (schemeOpenOverlapRestriction X i).mapDerivedCategory ≫
          (schemeDerivedOpenRestrictionCompIso X i).hom)
        (schemeDerivedDirectImage (U ⊓ V).ι)
  apply biprod.hom_ext'
  · simp only [biprod.inl_desc_assoc, biprod.inl_map_assoc, biprod.inl_desc]
    simpa only [ρ, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.comp_map, Functor.comp_obj,
      schemeDerivedOpenDirectImageRestriction, Adjunction.homEquiv_unit]
      using ((ρ (homOfLE (inf_le_left : U ⊓ V ≤ U)) adjU).naturality f).symm
  · simp only [biprod.inr_desc_assoc, biprod.inr_map_assoc,
      biprod.inr_desc, Preadditive.neg_comp, Preadditive.comp_neg]
    apply congrArg Neg.neg
    simpa only [ρ, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.comp_map, Functor.comp_obj,
      schemeDerivedOpenDirectImageRestriction, Adjunction.homEquiv_unit]
      using ((ρ (homOfLE (inf_le_right : U ⊓ V ≤ V)) adjV).naturality f).symm

private def representativeBoundary (X : Scheme.{u}) (U V : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (U ⊓ V).toScheme.toRingedSpace))]
    (adjW : (schemeOpenRestriction X (U ⊓ V)).mapDerivedCategory ⊣
      schemeDerivedDirectImage (U ⊓ V).ι)
    (hcover : U ⊔ V = ⊤)
    (I : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    [I.IsKInjective] (hI : ∀ n : ℤ, Injective (I.X n)) :
    (schemeDerivedDirectImage (U ⊓ V).ι).obj
      ((schemeOpenRestriction X (U ⊓ V)).mapDerivedCategory.obj (DerivedCategory.Q.obj I)) ⟶
        (DerivedCategory.Q.obj I)⟦(1 : ℤ)⟧ :=
  (schemeOpenModuleImageComplexComparison X (U ⊓ V) I adjW).inv ≫
    DerivedCategory.triangleOfSESδ
      (schemeMayerVietorisComplex_shortExact X U V hcover I hI)

private theorem representativeBoundary_naturality (X : Scheme.{u}) (U V : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (U ⊓ V).toScheme.toRingedSpace))]
    (adjW : (schemeOpenRestriction X (U ⊓ V)).mapDerivedCategory ⊣
      schemeDerivedDirectImage (U ⊓ V).ι)
    (hcover : U ⊔ V = ⊤)
    (I J : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    [I.IsKInjective] [J.IsKInjective]
    (hI : ∀ n : ℤ, Injective (I.X n)) (hJ : ∀ n : ℤ, Injective (J.X n))
    (f : I ⟶ J) :
    representativeBoundary X U V adjW hcover I hI ≫ (DerivedCategory.Q.map f)⟦(1 : ℤ)⟧' =
      (schemeDerivedDirectImage (U ⊓ V).ι).map
        ((schemeOpenRestriction X (U ⊓ V)).mapDerivedCategory.map (DerivedCategory.Q.map f)) ≫
          representativeBoundary X U V adjW hcover J hJ := by
  obtain ⟨m, hm₁, hm₃⟩ := concrete_map X U V I J f
  have hn := DerivedCategory.triangleOfSESδ_naturality
    (schemeMayerVietorisComplex_shortExact X U V hcover I hI)
    (schemeMayerVietorisComplex_shortExact X U V hcover J hJ) m
  rw [hm₁, hm₃] at hn
  dsimp only [representativeBoundary]
  rw [Category.assoc, hn]
  have hc := open_comparison_naturality X (U ⊓ V) I J f adjW
  rw [← Category.assoc, ← Category.assoc]
  apply congrArg (fun k => k ≫ DerivedCategory.triangleOfSESδ
    (schemeMayerVietorisComplex_shortExact X U V hcover J hJ))
  apply (cancel_mono (schemeOpenModuleImageComplexComparison X (U ⊓ V) J adjW).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [hc, Iso.inv_hom_id_assoc]

private theorem representativeBoundary_distinguished (X : Scheme.{u}) (U V : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (U ⊓ V).toScheme.toRingedSpace))]
    (adjU : (schemeOpenRestriction X U).mapDerivedCategory ⊣ schemeDerivedDirectImage U.ι)
    (adjV : (schemeOpenRestriction X V).mapDerivedCategory ⊣ schemeDerivedDirectImage V.ι)
    (adjW : (schemeOpenRestriction X (U ⊓ V)).mapDerivedCategory ⊣
      schemeDerivedDirectImage (U ⊓ V).ι)
    (hcover : U ⊔ V = ⊤)
    (I : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    [I.IsKInjective] (hI : ∀ n : ℤ, Injective (I.X n)) :
    Triangle.mk (biprod.lift (adjU.unit.app (DerivedCategory.Q.obj I))
      (adjV.unit.app (DerivedCategory.Q.obj I)))
      (biprod.desc
        (schemeDerivedOpenDirectImageRestriction X (homOfLE (inf_le_left : U ⊓ V ≤ U))
          adjU adjW (DerivedCategory.Q.obj I))
        (-(schemeDerivedOpenDirectImageRestriction X (homOfLE (inf_le_right : U ⊓ V ≤ V))
          adjV adjW (DerivedCategory.Q.obj I))))
      (representativeBoundary X U V adjW hcover I hI) ∈
        distTriang (schemeDerivedCategory X) := by
  let cU := schemeOpenModuleImageComplexComparison X U I adjU
  let cV := schemeOpenModuleImageComplexComparison X V I adjV
  let cW := schemeOpenModuleImageComplexComparison X (U ⊓ V) I adjW
  let Q : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ ⥤
    schemeDerivedCategory X := DerivedCategory.Q
  have : PreservesBinaryBiproducts Q := preservesBinaryBiproducts_of_preservesBiproducts Q
  let cB := Q.mapBiprod (schemeOpenModuleImageComplex X U I)
    (schemeOpenModuleImageComplex X V I) ≪≫ biprod.mapIso cU cV
  let T := Triangle.mk (biprod.lift (adjU.unit.app (DerivedCategory.Q.obj I))
      (adjV.unit.app (DerivedCategory.Q.obj I)))
    (biprod.desc
      (schemeDerivedOpenDirectImageRestriction X (homOfLE (inf_le_left : U ⊓ V ≤ U)) adjU adjW
        (DerivedCategory.Q.obj I))
      (-(schemeDerivedOpenDirectImageRestriction X (homOfLE (inf_le_right : U ⊓ V ≤ V)) adjV adjW
        (DerivedCategory.Q.obj I))))
    (representativeBoundary X U V adjW hcover I hI)
  let hs := schemeMayerVietorisComplex_shortExact X U V hcover I hI
  refine isomorphic_distinguished _ (DerivedCategory.triangleOfSES_distinguished hs) _ ?_
  refine (Triangle.isoMk (DerivedCategory.triangleOfSES hs) T (Iso.refl _) cB cW
    ?_ ?_ ?_).symm
  · change Q.map (schemeMayerVietorisF X U V I) ≫ cB.hom =
      𝟙 _ ≫ biprod.lift (adjU.unit.app _) (adjV.unit.app _)
    simp only [Category.id_comp]
    dsimp only [schemeMayerVietorisF, cB, Iso.trans_hom, biprod.mapIso]
    rw [← Category.assoc, biprod.map_lift_mapBiprod]
    apply biprod.hom_ext
    · simp only [Category.assoc, biprod.map_fst, biprod.lift_fst_assoc]
      erw [biprod.lift_fst]
      exact schemeOpenModuleImageComplexComparison_unit X U I adjU
    · simp only [Category.assoc, biprod.map_snd, biprod.lift_snd_assoc]
      erw [biprod.lift_snd]
      exact schemeOpenModuleImageComplexComparison_unit X V I adjV
  · change Q.map (schemeMayerVietorisG X U V I) ≫ cW.hom = cB.hom ≫ _
    dsimp only [T, Triangle.mk_mor₂, schemeMayerVietorisG, cB, Iso.trans_hom, biprod.mapIso]
    rw [← biprod.mapBiprod_hom_desc Q]
    simp only [Category.assoc]
    apply congrArg (fun k => (Q.mapBiprod
      (schemeOpenModuleImageComplex X U I) (schemeOpenModuleImageComplex X V I)).hom ≫ k)
    apply biprod.hom_ext'
    · simp only [biprod.inl_desc_assoc, biprod.inl_map_assoc]
      erw [biprod.inl_desc]
      exact schemeOpenModuleImageComplexComparison_restriction X
        (homOfLE (inf_le_left : U ⊓ V ≤ U)) I adjU adjW
    · simp only [biprod.inr_desc_assoc, biprod.inr_map_assoc, Functor.map_neg]
      erw [biprod.inr_desc]
      simpa only [Preadditive.comp_neg, Preadditive.neg_comp] using
        congrArg Neg.neg (schemeOpenModuleImageComplexComparison_restriction X
        (homOfLE (inf_le_right : U ⊓ V ≤ V)) I adjV adjW)
  · change DerivedCategory.triangleOfSESδ hs ≫ (𝟙 _)⟦(1 : ℤ)⟧' =
      cW.hom ≫ (cW.inv ≫ DerivedCategory.triangleOfSESδ hs)
    simp only [Iso.hom_inv_id_assoc]
    rw [CategoryTheory.Functor.map_id]
    exact Category.comp_id _


private theorem transport_boundary_square
    {C : Type*} [Category C] (H S : C ⥤ C) {A B E F : C}
    (e : A ≅ E) (d : B ≅ F) (a : H.obj A ⟶ S.obj A) (b : H.obj B ⟶ S.obj B)
    (f : A ⟶ B) (φ : E ⟶ F) (hf : f = e.hom ≫ φ ≫ d.inv)
    (ha : a ≫ S.map f = H.map f ≫ b) :
    (H.map e.inv ≫ a ≫ S.map e.hom) ≫ S.map φ =
      H.map φ ≫ (H.map d.inv ≫ b ≫ S.map d.hom) := by
  have ht : e.hom ≫ φ = f ≫ d.hom := by
    simp only [hf, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have ht' : e.inv ≫ f = φ ≫ d.inv := by
    simp only [hf, Iso.inv_hom_id_assoc]
  simp only [Category.assoc]
  rw [← S.map_comp, ht, S.map_comp, reassoc_of% ha]
  rw [← H.map_comp_assoc, ht', H.map_comp, Category.assoc]

private theorem canonicalMV_spec
    (X : Scheme.{u}) (U V : X.Opens) (hcover : U ⊔ V = ⊤)
    [d1 : HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [d2 : HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    [d3 : HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))]
    [d4 : HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (U ⊓ V).toScheme.toRingedSpace))] :
    (∀ E, schemeMVTriangle X U V hcover E ∈ distTriang (schemeDerivedCategory X)) ∧
    (∀ (E F : schemeDerivedCategory X) (φ : E ⟶ F),
      schemeMVBoundary X U V hcover E ≫ φ⟦(1 : ℤ)⟧' =
        (schemeDerivedDirectImage (U ⊓ V).ι).map
          ((schemeOpenRestriction X (U ⊓ V)).mapDerivedCategory.map φ) ≫
            schemeMVBoundary X U V hcover F) := by
  classical
  let I := schemeMVResolution.{u, w} X
  have hi (E : schemeDerivedCategory X) : (I E).IsKInjective := by
    dsimp only [I]
    infer_instance
  have hinj (E : schemeDerivedCategory X) (n : ℤ) : Injective ((I E).X n) := by
    dsimp only [I]
    infer_instance
  let e := schemeMVResolutionIso.{u, w} X
  let adj (W : X.Opens)
      [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace))] :=
    schemeMVAdjunction X W
  let aU := adj U
  let aV := adj V
  let aW := adj (U ⊓ V)
  let H := (schemeOpenRestriction X (U ⊓ V)).mapDerivedCategory ⋙
    schemeDerivedDirectImage (U ⊓ V).ι
  let δ (E : schemeDerivedCategory X) :=
    H.map (e E).inv ≫ representativeBoundary X U V aW hcover (I E) (hinj E) ≫
      (e E).hom⟦(1 : ℤ)⟧' 
  have hn (E F : schemeDerivedCategory X) (φ : E ⟶ F) :
      δ E ≫ φ⟦(1 : ℤ)⟧' = H.map φ ≫ δ F := by
    obtain ⟨f, hf⟩ := derived_map_surjective (I E) (I F)
      ((e E).hom ≫ φ ≫ (e F).inv)
    exact transport_boundary_square H (shiftFunctor _ (1 : ℤ)) (e E) (e F)
      (representativeBoundary X U V aW hcover (I E) (hinj E))
      (representativeBoundary X U V aW hcover (I F) (hinj F))
      (DerivedCategory.Q.map f) φ hf
      (representativeBoundary_naturality X U V aW hcover
        (I E) (I F) (hinj E) (hinj F) f)
  have hδ (E : schemeDerivedCategory X) : schemeMVBoundary X U V hcover E = δ E := by
    dsimp only [schemeMVBoundary, δ, H, I, e, representativeBoundary, aW, adj,
      schemeMVDerivedRestriction]
  dsimp only [schemeMVTriangle]
  simp only [hδ]
  refine ⟨?_, hn⟩
  · intro E
    have hd := representativeBoundary_distinguished X U V aU aV aW hcover (I E) (hinj E)
    refine isomorphic_distinguished _ hd _ ?_
    let HU := (schemeOpenRestriction X U).mapDerivedCategory ⋙ schemeDerivedDirectImage U.ι
    let HV := (schemeOpenRestriction X V).mapDerivedCategory ⋙ schemeDerivedDirectImage V.ι
    refine (Triangle.isoMk _ _ (e E)
      (biprod.mapIso (HU.mapIso (e E)) (HV.mapIso (e E))) (H.mapIso (e E))
      (mv_comm₁ X U V aU aV (e E).hom)
      (mv_comm₂ X U V aU aV aW (e E).hom) ?_).symm
    change representativeBoundary X U V aW hcover (I E) (hinj E) ≫
      (e E).hom⟦(1 : ℤ)⟧' = H.map (e E).hom ≫ δ E
    simp only [δ, ← H.map_comp_assoc,
      Iso.hom_inv_id, H.map_id, Category.id_comp]

/-- Mayer--Vietoris boundaries can be chosen simultaneously, naturally in the object.
The adjunction units and the difference of restrictions are the first two maps.
Source: Stacks, Tag 08BV (blueprint: lem-pc-derived-mayer-vietoris-functorial).

Proof:
1. Choose K-injective representatives with injective terms
   (prop-pur-kinjective-resolutions-exist). Restriction preserves K-injectivity
   (lem-sc-derived-k-injective-restrict-open). The Mayer--Vietoris sequence is exact
   degreewise by injective restriction surjectivity
   (lem-sc-ringed-space-injective-restriction-surjective).
2. Represent derived morphisms by chain maps into K-injective representatives
   (lem-sc-kinjective-quasi-iso-comparison). Restriction gives a morphism of the
   short exact sequences. Naturality of triangleOfSES, including its boundary,
   gives the three commuting squares (lem-weil-pbc-complex-ses-triangle).
3. For direct image, apply the triangulated right derived functor
   (lem-pc-right-derived-functor-triangulated). Choose a K-injective representative
   J of h_*I' and a quasi-isomorphism h_*I' → J. Its restrictions give the
   comparison of the middle and intersection terms, using derived direct-image
   composition (lem-pc-derived-direct-image-composition) and open restriction
   (lem-pc-restrict-derived-direct-image-open).
4. The source sequence is degreewise split because I' has injective terms. Its
   other complexes are K-injective by restriction and the exact-left-adjoint
   criterion (lem-weil-pbc-right-adjoint-preserves-kinjective). Apply
   lem-pc-derived-functor-termwise-split-ses-triangle to identify the image
   boundary with the boundary of the image sequence. Naturality of triangleOfSES
   applied to q and its restrictions gives the final square, hence an isomorphism
   of distinguished triangles. Quasi-coherence of Rh_*E' follows from
   lem-pc-derived-direct-image-preserves-qcoh.
-/
theorem schemeDerived_mayerVietoris_naturality
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (U V : X.Opens) (hU : IsCompact (U : Set X)) (hV : IsCompact (V : Set X))
    (hcover : U ⊔ V = ⊤)
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      (moduleRings U.toScheme.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      (moduleRings V.toScheme.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      (moduleRings (U ⊓ V).toScheme.toRingedSpace))] :
    ∃ (adjU : (schemeOpenRestriction X U).mapDerivedCategory ⊣
        schemeDerivedDirectImage U.ι)
      (adjV : (schemeOpenRestriction X V).mapDerivedCategory ⊣
        schemeDerivedDirectImage V.ι)
      (adjUV : (schemeOpenRestriction X (U ⊓ V)).mapDerivedCategory ⊣
        schemeDerivedDirectImage (U ⊓ V).ι)
      (δ : ∀ E : schemeDerivedCategory X,
        (schemeDerivedDirectImage (U ⊓ V).ι).obj
          ((schemeOpenRestriction X (U ⊓ V)).mapDerivedCategory.obj E) ⟶ E⟦(1 : ℤ)⟧),
      (∀ (E : schemeDerivedCategory X), schemeDerivedQCohProperty X E →
        Triangle.mk (biprod.lift (adjU.unit.app E) (adjV.unit.app E))
        (biprod.desc
          (schemeDerivedOpenDirectImageRestriction X (homOfLE inf_le_left)
            adjU adjUV E)
          (-(schemeDerivedOpenDirectImageRestriction X (homOfLE inf_le_right)
            adjV adjUV E))) (δ E) ∈ distTriang (schemeDerivedCategory X)) ∧
      ∀ (E F : schemeDerivedCategory X),
        schemeDerivedQCohProperty X E → schemeDerivedQCohProperty X F →
        ∀ φ : E ⟶ F,
          ∃ m : (Triangle.mk (biprod.lift (adjU.unit.app E) (adjV.unit.app E))
        (biprod.desc
          (schemeDerivedOpenDirectImageRestriction X (homOfLE inf_le_left)
            adjU adjUV E)
          (-(schemeDerivedOpenDirectImageRestriction X (homOfLE inf_le_right)
            adjV adjUV E))) (δ E)) ⟶
            (Triangle.mk (biprod.lift (adjU.unit.app F) (adjV.unit.app F))
        (biprod.desc
          (schemeDerivedOpenDirectImageRestriction X (homOfLE inf_le_left)
            adjU adjUV F)
          (-(schemeDerivedOpenDirectImageRestriction X (homOfLE inf_le_right)
            adjV adjUV F))) (δ F)),
            m.hom₁ = φ ∧
            m.hom₂ = biprod.map
              ((schemeDerivedDirectImage U.ι).map
          ((schemeOpenRestriction X U).mapDerivedCategory.map φ))
              ((schemeDerivedDirectImage V.ι).map
          ((schemeOpenRestriction X V).mapDerivedCategory.map φ)) ∧
            m.hom₃ = (schemeDerivedDirectImage (U ⊓ V).ι).map
          ((schemeOpenRestriction X (U ⊓ V)).mapDerivedCategory.map φ) := by
  classical
  rename_i d1 d2 d3 d4
  have _ := hU
  have _ := hV
  have hs := @canonicalMV_spec.{u, w} X U V hcover d1 d2 d3 d4
  have hd := hs.1
  have hn := hs.2
  refine ⟨schemeMVAdjunction X U, schemeMVAdjunction X V,
    schemeMVAdjunction X (U ⊓ V), schemeMVBoundary X U V hcover, ?_, ?_⟩
  · intro E _
    exact hd E
  · intro E F _ _ φ
    refine ⟨⟨φ, biprod.map
      ((schemeDerivedDirectImage U.ι).map
        ((schemeOpenRestriction X U).mapDerivedCategory.map φ))
      ((schemeDerivedDirectImage V.ι).map
        ((schemeOpenRestriction X V).mapDerivedCategory.map φ)),
      (schemeDerivedDirectImage (U ⊓ V).ι).map
        ((schemeOpenRestriction X (U ⊓ V)).mapDerivedCategory.map φ),
      mv_comm₁ X U V (schemeMVAdjunction.{u, w} X U)
        (schemeMVAdjunction.{u, w} X V) φ,
      mv_comm₂ X U V (schemeMVAdjunction.{u, w} X U)
        (schemeMVAdjunction.{u, w} X V) (schemeMVAdjunction.{u, w} X (U ⊓ V)) φ,
      hn E F φ⟩,
      rfl, rfl, rfl⟩

private theorem first_square_identity
    {C : Type*} [Category C] {A B D : C}
    (a : A ⟶ B) (c : B ⟶ D) (b : A ⟶ D) (ha : a ≫ c = b) :
    a ≫ c = (𝟙 A) ≫ b := by
  rw [Category.id_comp]
  exact ha

private theorem boundary_square_identity
    {C : Type*} [Category C] (S : C ⥤ C) {A B D : C}
    (a : A ⟶ S.obj B) (c : A ⟶ D) (b : D ⟶ S.obj B) (ha : a = c ≫ b) :
    a ≫ S.map (𝟙 B) = c ≫ b := by
  rw [S.map_id, Category.comp_id]
  exact ha

set_option backward.isDefEq.respectTransparency true in
/-- The image Mayer--Vietoris triangle is identified with the target one by
composition and open-restriction comparison isomorphisms, with identity first component.
The comparison functor isomorphisms are the normalized constructions
`schemeMVDirectImageComposition` and `schemeMVOpenRestrictionComparison`,
with the determining right-derived unit equation and sectionwise restriction identity,
the same for every object.
The triangle isomorphism includes compatibility with the connecting maps.
Source: Stacks, Tags 08BV, 0D5T and 0DJ9
(blueprint: lem-pc-derived-mayer-vietoris-functorial).

Proof:
1. Choose K-injective representatives with injective terms
   (prop-pur-kinjective-resolutions-exist). Restriction preserves K-injectivity
   (lem-sc-derived-k-injective-restrict-open). The Mayer--Vietoris sequence is exact
   degreewise by injective restriction surjectivity
   (lem-sc-ringed-space-injective-restriction-surjective).
2. Represent derived morphisms by chain maps into K-injective representatives
   (lem-sc-kinjective-quasi-iso-comparison). Restriction gives a morphism of the
   short exact sequences. Naturality of triangleOfSES, including its boundary,
   gives the three commuting squares (lem-weil-pbc-complex-ses-triangle).
3. For direct image, apply the triangulated right derived functor
   (lem-pc-right-derived-functor-triangulated). Choose a K-injective representative
   J of h_*I' and a quasi-isomorphism h_*I' → J. Its restrictions give the
   comparison of the middle and intersection terms, using derived direct-image
   composition (lem-pc-derived-direct-image-composition) and open restriction
   (lem-pc-restrict-derived-direct-image-open).
4. The source sequence is degreewise split because I' has injective terms. Its
   other complexes are K-injective by restriction and the exact-left-adjoint
   criterion (lem-weil-pbc-right-adjoint-preserves-kinjective). Apply
   lem-pc-derived-functor-termwise-split-ses-triangle to identify the image
   boundary with the boundary of the image sequence. Naturality of triangleOfSES
   applied to q and its restrictions gives the final square, hence an isomorphism
   of distinguished triangles. Quasi-coherence of Rh_*E' follows from
   lem-pc-derived-direct-image-preserves-qcoh.
-/
theorem schemeDerived_mayerVietoris_directImage
    (X Y : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    (h : X ⟶ Y) [QuasiCompact h] [QuasiSeparated h]
    (U V : Y.Opens) (hU : IsCompact (U : Set Y)) (hV : IsCompact (V : Set Y))
    (hcover : U ⊔ V = ⊤)
    (hU' : IsCompact ((h ⁻¹ᵁ U) : Set X))
    (hV' : IsCompact ((h ⁻¹ᵁ V) : Set X))
    [d1 : HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [d2 : HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [d3 : ∀ T : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.toScheme.toRingedSpace))]
    [d4 : ∀ T : Y.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.toScheme.toRingedSpace))]
    :
    ∃ (adjU : (schemeMVDerivedRestriction Y U) ⊣
        schemeDerivedDirectImage U.ι)
      (adjV : (schemeMVDerivedRestriction Y V) ⊣
        schemeDerivedDirectImage V.ι)
      (adjUV : (schemeMVDerivedRestriction Y (U ⊓ V)) ⊣
        schemeDerivedDirectImage (U ⊓ V).ι)
      (δ : ∀ E : schemeDerivedCategory Y,
        (schemeDerivedDirectImage (U ⊓ V).ι).obj
          ((schemeMVDerivedRestriction Y (U ⊓ V)).obj E) ⟶ E⟦(1 : ℤ)⟧)
      (adjU' : (schemeMVDerivedRestriction X (h ⁻¹ᵁ U)) ⊣
        schemeDerivedDirectImage (h ⁻¹ᵁ U).ι)
      (adjV' : (schemeMVDerivedRestriction X (h ⁻¹ᵁ V)) ⊣
        schemeDerivedDirectImage (h ⁻¹ᵁ V).ι)
      (adjUV' : (schemeMVDerivedRestriction X ((h ⁻¹ᵁ U) ⊓ (h ⁻¹ᵁ V))) ⊣
        schemeDerivedDirectImage ((h ⁻¹ᵁ U) ⊓ (h ⁻¹ᵁ V)).ι)
      (δ' : ∀ E : schemeDerivedCategory X,
        (schemeDerivedDirectImage ((h ⁻¹ᵁ U) ⊓ (h ⁻¹ᵁ V)).ι).obj
          ((schemeMVDerivedRestriction X ((h ⁻¹ᵁ U) ⊓ (h ⁻¹ᵁ V))).obj E) ⟶ E⟦(1 :
            ℤ)⟧),
      (∀ (E F : schemeDerivedCategory X),
        schemeDerivedQCohProperty X E → schemeDerivedQCohProperty X F →
        ∀ φ : E ⟶ F,
          δ' E ≫ φ⟦(1 : ℤ)⟧' =
            (schemeDerivedDirectImage ((h ⁻¹ᵁ U) ⊓ (h ⁻¹ᵁ V)).ι).map
              ((schemeMVDerivedRestriction X ((h ⁻¹ᵁ U) ⊓ (h ⁻¹ᵁ V))).map φ) ≫ δ' F) ∧
      (∀ (E F : schemeDerivedCategory Y),
        schemeDerivedQCohProperty Y E → schemeDerivedQCohProperty Y F →
        ∀ φ : E ⟶ F,
          δ E ≫ φ⟦(1 : ℤ)⟧' =
            (schemeDerivedDirectImage (U ⊓ V).ι).map
              ((schemeMVDerivedRestriction Y (U ⊓ V)).map φ) ≫ δ F) ∧
      ∀ (E : schemeDerivedCategory X), schemeDerivedQCohProperty X E →
      schemeDerivedQCohProperty Y ((schemeDerivedDirectImage h).obj E) ∧
      (Triangle.mk (biprod.lift (adjU'.unit.app E) (adjV'.unit.app E))
        (biprod.desc
          (schemeDerivedOpenDirectImageRestriction X
            (homOfLE (inf_le_left : (h ⁻¹ᵁ U) ⊓ (h ⁻¹ᵁ V) ≤ h ⁻¹ᵁ U))
            adjU' adjUV' E)
          (-(schemeDerivedOpenDirectImageRestriction X
            (homOfLE (inf_le_right : (h ⁻¹ᵁ U) ⊓ (h ⁻¹ᵁ V) ≤ h ⁻¹ᵁ V))
            adjV' adjUV' E))) (δ' E)) ∈ distTriang (schemeDerivedCategory X) ∧
      (Triangle.mk (biprod.lift (adjU.unit.app ((schemeDerivedDirectImage h).obj E))
            (adjV.unit.app ((schemeDerivedDirectImage h).obj E)))
        (biprod.desc
          (schemeDerivedOpenDirectImageRestriction Y (homOfLE (inf_le_left : U ⊓ V ≤ U))
            adjU adjUV ((schemeDerivedDirectImage h).obj E))
          (-(schemeDerivedOpenDirectImageRestriction Y (homOfLE (inf_le_right : U ⊓ V ≤ V))
            adjV adjUV ((schemeDerivedDirectImage h).obj E)))) (δ ((schemeDerivedDirectImage
            h).obj E))) ∈ distTriang (schemeDerivedCategory Y) ∧
      schemeMVImageTriangle h (Triangle.mk (biprod.lift (adjU'.unit.app E)
            (adjV'.unit.app E))
        (biprod.desc
          (schemeDerivedOpenDirectImageRestriction X
            (homOfLE (inf_le_left : (h ⁻¹ᵁ U) ⊓ (h ⁻¹ᵁ V) ≤ h ⁻¹ᵁ U))
            adjU' adjUV' E)
          (-(schemeDerivedOpenDirectImageRestriction X
            (homOfLE (inf_le_right : (h ⁻¹ᵁ U) ⊓ (h ⁻¹ᵁ V) ≤ h ⁻¹ᵁ V))
            adjV' adjUV' E))) (δ' E)) ∈
        distTriang (schemeDerivedCategory Y) ∧
      ∃ (cU : (schemeDerivedDirectImage h).obj ((schemeDerivedDirectImage (h ⁻¹ᵁ U).ι).obj
          ((schemeMVDerivedRestriction X (h ⁻¹ᵁ U)).obj E)) ≅
          (schemeDerivedDirectImage U.ι).obj
          ((schemeMVDerivedRestriction Y U).obj ((schemeDerivedDirectImage h).obj E)))
        (cV : (schemeDerivedDirectImage h).obj ((schemeDerivedDirectImage (h ⁻¹ᵁ V).ι).obj
          ((schemeMVDerivedRestriction X (h ⁻¹ᵁ V)).obj E)) ≅
          (schemeDerivedDirectImage V.ι).obj
          ((schemeMVDerivedRestriction Y V).obj ((schemeDerivedDirectImage h).obj E)))
        (cUV : (schemeDerivedDirectImage h).obj ((schemeDerivedDirectImage ((h ⁻¹ᵁ U) ⊓ (h ⁻¹ᵁ
            V)).ι).obj
          ((schemeMVDerivedRestriction X ((h ⁻¹ᵁ U) ⊓ (h ⁻¹ᵁ V))).obj E)) ≅
          (schemeDerivedDirectImage (U ⊓ V).ι).obj
          ((schemeMVDerivedRestriction Y (U ⊓ V)).obj ((schemeDerivedDirectImage
            h).obj E)))
        (e : schemeMVImageTriangle h (Triangle.mk (biprod.lift
            (adjU'.unit.app E) (adjV'.unit.app E))
        (biprod.desc
          (schemeDerivedOpenDirectImageRestriction X
            (homOfLE (inf_le_left : (h ⁻¹ᵁ U) ⊓ (h ⁻¹ᵁ V) ≤ h ⁻¹ᵁ U))
            adjU' adjUV' E)
          (-(schemeDerivedOpenDirectImageRestriction X
            (homOfLE (inf_le_right : (h ⁻¹ᵁ U) ⊓ (h ⁻¹ᵁ V) ≤ h ⁻¹ᵁ V))
            adjV' adjUV' E))) (δ' E)) ≅
          (Triangle.mk (biprod.lift (adjU.unit.app ((schemeDerivedDirectImage h).obj E))
            (adjV.unit.app ((schemeDerivedDirectImage h).obj E)))
        (biprod.desc
          (schemeDerivedOpenDirectImageRestriction Y (homOfLE (inf_le_left : U ⊓ V ≤ U))
            adjU adjUV ((schemeDerivedDirectImage h).obj E))
          (-(schemeDerivedOpenDirectImageRestriction Y (homOfLE (inf_le_right : U ⊓ V ≤ V))
            adjV adjUV ((schemeDerivedDirectImage h).obj E)))) (δ ((schemeDerivedDirectImage
            h).obj E)))),
        cU.hom = (schemeMVOpenComparison h U E).hom ∧
        cV.hom = (schemeMVOpenComparison h V E).hom ∧
        cUV.hom = (schemeMVOpenComparison h (U ⊓ V) E).hom ∧
        e.hom.hom₁ = 𝟙 ((schemeDerivedDirectImage h).obj E) ∧
        e.hom.hom₂ = biprod.lift
          ((schemeDerivedDirectImage h).map biprod.fst ≫ cU.hom)
          ((schemeDerivedDirectImage h).map biprod.snd ≫ cV.hom) ∧
        e.hom.hom₃ = cUV.hom := by
  classical
  have _ := hU
  have _ := hV
  have _ := hU'
  have _ := hV'
  have hcover' : (h ⁻¹ᵁ U) ⊔ (h ⁻¹ᵁ V) = ⊤ := by
    rw [← Scheme.Hom.preimage_sup, hcover, Scheme.Hom.preimage_top]
  have hsX := @canonicalMV_spec.{u, w} X (h ⁻¹ᵁ U) (h ⁻¹ᵁ V) hcover'
    d1 (d3 _) (d3 _) (d3 _)
  have hdX := hsX.1
  have hnX := hsX.2
  have hsY := @canonicalMV_spec.{u, w} Y U V hcover
    d2 (d4 U) (d4 V) (d4 (U ⊓ V))
  have hdY := hsY.1
  have hnY := hsY.2
  refine ⟨schemeMVAdjunction Y U, schemeMVAdjunction Y V,
    schemeMVAdjunction Y (U ⊓ V), schemeMVBoundary Y U V hcover,
    schemeMVAdjunction X (h ⁻¹ᵁ U), schemeMVAdjunction X (h ⁻¹ᵁ V),
    schemeMVAdjunction X ((h ⁻¹ᵁ U) ⊓ (h ⁻¹ᵁ V)),
    schemeMVBoundary X (h ⁻¹ᵁ U) (h ⁻¹ᵁ V) hcover', ?_, ?_, ?_⟩
  · intro E F _ _ φ
    exact hnX E F φ
  · intro E F _ _ φ
    exact hnY E F φ
  · intro E hE
    refine ⟨schemeDerivedDirectImage_preserves_QCoh h E hE, hdX E,
      hdY ((schemeDerivedDirectImage.{u, w, w} h).obj E),
      schemeMVImageTriangle_distinguished.{u, w} h
        (schemeMVTriangle.{u, w} X (h ⁻¹ᵁ U) (h ⁻¹ᵁ V) hcover' E) (hdX E), ?_⟩
    let cU := schemeMVOpenComparison h U E
    let cV := schemeMVOpenComparison h V E
    let cW := schemeMVOpenComparison h (U ⊓ V) E
    have hc := @schemeMV_directImage_squares.{u, w} X Y h U V hcover hcover'
      d1 d2 d3 d4 E
    have hc₁ := hc.1
    have hc₂ := hc.2
    have hc₃ := @schemeMV_directImage_boundary.{u, w} X Y h U V hcover hcover'
      d1 d2 d3 d4 E
    let e := Triangle.isoMk
      (schemeMVImageTriangle h
        (schemeMVTriangle X (h ⁻¹ᵁ U) (h ⁻¹ᵁ V) hcover' E))
      (schemeMVTriangle Y U V hcover ((schemeDerivedDirectImage h).obj E))
      (Iso.refl _) (schemeMVMiddleComparison h U V E) cW
      (first_square_identity _ _ _ hc₁) hc₂
      (boundary_square_identity (shiftFunctor _ (1 : ℤ)) _ cW.hom _ hc₃)
    refine ⟨cU, cV, cW, e, rfl, rfl, rfl, rfl, ?_, rfl⟩
    change (schemeMVMiddleComparison h U V E).hom = _
    unfold schemeMVMiddleComparison
    dsimp only [Iso.trans_hom, biprod.mapIso]
    apply biprod.hom_ext
    · simp only [Category.assoc, biprod.map_fst]
      simp only [Functor.mapBiprod_hom, biprod.lift_fst_assoc]
      exact (biprod.lift_fst _ _).symm
    · simp only [Category.assoc, biprod.map_snd]
      simp only [Functor.mapBiprod_hom, biprod.lift_snd_assoc]
      exact (biprod.lift_snd _ _).symm

end AlgebraicGeometry
