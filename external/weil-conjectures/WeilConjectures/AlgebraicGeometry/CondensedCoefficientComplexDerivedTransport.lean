/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CondensedCoefficientComplexDiagram

/-! # Exact localization of coefficient-complex adjunction mates -/

@[expose] public section
universe u v
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace CategoryTheory.Mod
open MonoidalCategory
variable {A : Type u} [Category.{v} A] [Abelian A] [MonoidalCategory A]
  [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [IsGrothendieckAbelian.{v} A] [Abelian.HasFunctorialFlatResolution A]
  {R S : A} [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
  (φ : R ⟶ S) [IsMonHom φ] [PreservesFiniteLimits (extendScalars φ)]

omit [IsCommMonObj S] in
private lemma exact_unit_complex (K : CochainComplex (Mod A R) ℤ) :
    (extendRestrictAdjunction φ).mapDerivedCategoryAdjunction.unit.app
        (DerivedCategory.Q.obj K) ≫
      (comap φ).mapDerivedCategory.map
        ((extendScalars φ).mapDerivedCategoryFactors.hom.app K) ≫
      (comap φ).mapDerivedCategoryFactors.hom.app
        (((extendScalars φ).mapHomologicalComplex (.up ℤ)).obj K) =
    DerivedCategory.Q.map
      (((extendRestrictAdjunction φ).mapHomologicalComplex (.up ℤ)).unit.app K) := by
  let F := extendScalars φ
  let G : Mod A S ⥤ Mod A R := comap φ
  let adj : F ⊣ G := extendRestrictAdjunction φ
  have h := adj.mapDerivedCategoryAdjunction_unit_app_fac
    ((HomotopyCategory.quotient _ (.up ℤ)).obj K)
  rw [Adjunction.mapHomotopyCategory_unit_app_quotient] at h
  have hG := G.mapDerivedCategoryFactorsh_hom_app
    ((F.mapHomologicalComplex (.up ℤ)).obj K)
  erw [F.mapDerivedCategoryFactorsh_hom_app, hG] at h
  simp only [CategoryTheory.Functor.mapHomotopyCategoryFactors,
    Quotient.lift.isLift_inv, CategoryTheory.Functor.map_comp, Category.assoc] at h
  simp only [CategoryTheory.Functor.comp_obj, CategoryTheory.Functor.map_id,
    Category.id_comp, Category.comp_id] at h
  have hu := adj.mapDerivedCategoryAdjunction.unit.naturality
    ((DerivedCategory.quotientCompQhIso (Mod A R)).hom.app K)
  simp only [CategoryTheory.Functor.id_map, CategoryTheory.Functor.comp_map] at hu
  have hh := congrArg (fun k ↦ k ≫
    (DerivedCategory.quotientCompQhIso (Mod A R)).hom.app
      ((G.mapHomologicalComplex (.up ℤ)).obj
        ((F.mapHomologicalComplex (.up ℤ)).obj K))) h
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id] at hh
  rw [← reassoc_of% hu, DerivedCategory.quotientCompQhIso_hom_naturality] at hh
  have hc := G.mapDerivedCategory.map_comp
    ((DerivedCategory.quotientCompQhIso (Mod A S)).inv.app
      ((F.mapHomologicalComplex (.up ℤ)).obj K))
    ((DerivedCategory.quotientCompQhIso (Mod A S)).hom.app
      ((F.mapHomologicalComplex (.up ℤ)).obj K))
  simp only [Iso.inv_hom_id_app, CategoryTheory.Functor.map_id] at hc
  rw [reassoc_of% hc.symm] at hh
  exact (cancel_epi ((DerivedCategory.quotientCompQhIso (Mod A R)).hom.app K)).mp hh

@[reassoc]
private lemma derived_unit_comp_exact (M : DerivedCategory (Mod A R)) :
    (derivedExtendMapDerivedCategoryAdjunction φ).unit.app M ≫
      (comap φ).mapDerivedCategory.map
        ((extendScalars φ).leftDerivedFunctorIsoMapDerivedCategory.hom.app M) =
    (extendRestrictAdjunction φ).mapDerivedCategoryAdjunction.unit.app M := by
  simp only [derivedExtendMapDerivedCategoryAdjunction, derivedExtendRestrictAdjunction,
    rightDerivedComapIsoMapDerivedCategory, Adjunction.mapDerivedCategoryAdjunction,
    Adjunction.ofNatIsoLeft_unit, Adjunction.ofNatIsoRight_unit,
    NatTrans.comp_app, CategoryTheory.Functor.whiskerRight_app,
    CategoryTheory.Functor.whiskerLeft_app, Category.assoc]
  rw [← (comap φ).rightDerivedFunctorIsoMapDerivedCategory.hom.naturality]

private lemma derived_mate_complex (K : CochainComplex (Mod A R) ℤ)
    (L : CochainComplex (Mod A S) ℤ)
    (a : ((extendScalars φ).mapHomologicalComplex (.up ℤ)).obj K ⟶ L) :
    (derivedExtendMapDerivedCategoryAdjunction φ).homEquiv
      (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L)
      (((extendScalars φ).leftDerivedFunctorIsoMapDerivedCategory.hom.app
          (DerivedCategory.Q.obj K) ≫
          (extendScalars φ).mapDerivedCategoryFactors.hom.app K) ≫
        DerivedCategory.Q.map a) =
      DerivedCategory.Q.map
        ((((extendRestrictAdjunction φ).mapHomologicalComplex (.up ℤ)).homEquiv K L) a) ≫
        (comap φ).mapDerivedCategoryFactors.inv.app L := by
  apply (cancel_mono ((comap φ).mapDerivedCategoryFactors.hom.app L)).mp
  simp only [Adjunction.homEquiv_unit, CategoryTheory.Functor.map_comp, Category.assoc,
    Iso.inv_hom_id_app]
  rw [(comap φ).mapDerivedCategoryFactors_hom_naturality]
  erw [derived_unit_comp_exact_assoc φ, reassoc_of% exact_unit_complex φ K]
  dsimp only [CategoryTheory.Functor.comp_obj]
  rw [Category.comp_id]

private lemma derived_mate_counit (L : CochainComplex (Mod A S) ℤ) :
    (derivedExtendMapDerivedCategoryAdjunction φ).homEquiv
      (DerivedCategory.Q.obj (((comap φ).mapHomologicalComplex (.up ℤ)).obj L))
      (DerivedCategory.Q.obj L)
      (((extendScalars φ).leftDerivedFunctorIsoMapDerivedCategory.hom.app
          (DerivedCategory.Q.obj (((comap φ).mapHomologicalComplex (.up ℤ)).obj L)) ≫
          (extendScalars φ).mapDerivedCategoryFactors.hom.app
            (((comap φ).mapHomologicalComplex (.up ℤ)).obj L)) ≫
        DerivedCategory.Q.map
          (((extendRestrictAdjunction φ).mapHomologicalComplex (.up ℤ)).counit.app L)) =
      (comap φ).mapDerivedCategoryFactors.inv.app L := by
  let a := (extendRestrictAdjunction φ).mapHomologicalComplex (.up ℤ)
  have hm := derived_mate_complex φ (((comap φ).mapHomologicalComplex (.up ℤ)).obj L)
    L (a.counit.app L)
  have ht : a.homEquiv _ _ (a.counit.app L) = 𝟙 _ := a.right_triangle_components L
  change _ = DerivedCategory.Q.map (a.homEquiv _ _ (a.counit.app L)) ≫ _ at hm
  conv_rhs at hm => rw [ht, CategoryTheory.Functor.map_id, Category.id_comp]
  exact hm

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

private lemma exact_comparison_complex
    {T : A} [MonObj T] [IsCommMonObj T]
    (F : Mod A R ⥤ Mod A S) (G : Mod A S ⥤ Mod A T) (H : Mod A R ⥤ Mod A T)
    [F.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (e : F ⋙ G ≅ H) (K : CochainComplex (Mod A R) ℤ) :
    (((CategoryTheory.Functor.leftDerivedFunctorCompIso F G).symm ≪≫
      CategoryTheory.Functor.leftDerivedFunctorNatIso (F ⋙ G) e).hom.app
        (DerivedCategory.Q.obj K)) ≫
      H.leftDerivedFunctorIsoMapDerivedCategory.hom.app (DerivedCategory.Q.obj K) ≫
      H.mapDerivedCategoryFactors.hom.app K =
    G.leftDerivedFunctor.map
        (F.leftDerivedFunctorIsoMapDerivedCategory.hom.app (DerivedCategory.Q.obj K)) ≫
      G.leftDerivedFunctor.map (F.mapDerivedCategoryFactors.hom.app K) ≫
      G.leftDerivedFunctorIsoMapDerivedCategory.hom.app
        (DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj K)) ≫
      G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app K) := by
  simp only [CategoryTheory.Functor.leftDerivedFunctorCompIso,
    CategoryTheory.Functor.leftDerivedFunctorNatIso, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Iso.symm_inv, CategoryTheory.Functor.isoWhiskerRight_inv,
    CategoryTheory.Functor.isoWhiskerLeft_inv, NatTrans.comp_app,
    CategoryTheory.Functor.whiskerRight_app, CategoryTheory.Functor.whiskerLeft_app,
    Category.assoc, Iso.inv_hom_id_app_assoc]
  have hn₁ := G.leftDerivedFunctorIsoMapDerivedCategory.hom.naturality
    (F.mapDerivedCategoryFactors.hom.app K)
  have hn₂ := G.leftDerivedFunctorIsoMapDerivedCategory.hom.naturality
    (F.leftDerivedFunctorIsoMapDerivedCategory.hom.app (DerivedCategory.Q.obj K))
  conv_rhs =>
    arg 2
    rw [reassoc_of% hn₁]
  conv_rhs => rw [reassoc_of% hn₂]
  conv_lhs =>
    arg 2
    arg 2
    arg 2
    rw [CategoryTheory.Functor.mapDerivedCategoryNatIso_fac e K]
  conv_lhs =>
    arg 2
    arg 2
    arg 2
    arg 1
    rw [← CategoryTheory.Functor.mapDerivedCategoryCompIso_fac F G K]
  have hc : (CategoryTheory.Functor.mapHomologicalComplexCompIso
      (Iso.refl (F ⋙ G)) (.up ℤ)).hom.app K = 𝟙 _ := by
    ext n
    rfl
  erw [hc, CategoryTheory.Functor.map_id]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  erw [Category.id_comp]

omit [IsCommMonObj S] in
private lemma exact_comparison_naturality
    (F : Mod A R ⥤ Mod A S) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {K L : CochainComplex (Mod A R) ℤ} (f : K ⟶ L) :
    F.leftDerivedFunctor.map (DerivedCategory.Q.map f) ≫
        (F.leftDerivedFunctorIsoMapDerivedCategory.hom.app (DerivedCategory.Q.obj L) ≫
          F.mapDerivedCategoryFactors.hom.app L) =
      (F.leftDerivedFunctorIsoMapDerivedCategory.hom.app (DerivedCategory.Q.obj K) ≫
        F.mapDerivedCategoryFactors.hom.app K) ≫
          DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map f) := by
  rw [F.leftDerivedFunctorIsoMapDerivedCategory.hom.naturality_assoc,
    F.mapDerivedCategoryFactors_hom_naturality, Category.assoc]

end CategoryTheory.Mod

private lemma iso_map_cancel
    {D E : Type*} [Category D] [Category E] (F : D ⥤ E)
    {A : E} {B C : D} (f : A ⟶ F.obj C) (i : B ≅ C) :
    (f ≫ F.map i.inv) ≫ F.map i.hom = f := by
  rw [Category.assoc, ← F.map_comp, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.comp_id]

private lemma adjoint_comparison_triangle
    {D E : Type*} [Category D] [Category E] {F : D ⥤ E} {G : E ⥤ D}
    (a : F ⊣ G) {A : D} {B C : E} (i : A ≅ G.obj B) (u : B ≅ C)
    (z : F.obj A ⟶ C) (hz : a.homEquiv A C z = i.hom ≫ G.map u.hom) :
    (a.homEquiv A B).symm i.hom ≫ u.hom = z := by
  apply (a.homEquiv A C).injective
  rw [a.homEquiv_naturality_right, Equiv.apply_symm_apply, hz]

private lemma adjoint_comparison_target
    {D E : Type*} [Category D] [Category E] {F : D ⥤ E} {G : E ⥤ D}
    (a : F ⊣ G) {A W : D} {B C : E} (d : F.obj A ⟶ B) (v : B ≅ C)
    (f : G.obj C ≅ W) (q : A ⟶ W)
    (h : a.homEquiv A C (d ≫ v.hom) = q ≫ f.inv) :
    a.homEquiv A B d = q ≫ (f.symm ≪≫ G.mapIso v.symm).hom := by
  apply (cancel_mono (G.map v.hom)).mp
  simp only [Iso.trans_hom, Iso.symm_hom, CategoryTheory.Functor.mapIso_hom,
    Category.assoc]
  rw [← G.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.comp_id]
  exact (a.homEquiv_naturality_right d v.hom).symm.trans h

private lemma mate_transport_word
    {D E : Type*} [Category D] [Category E] (b : D ⥤ E)
    {A B C Z : D} (m : A ⟶ B) (u : B ⟶ C) (z : A ⟶ Z) (q : Z ⟶ C)
    {P Q V W U T : E} (tE : b.obj A ≅ P) (tF : b.obj B ≅ Q)
    (v : Q ⟶ T) (ve : P ⟶ V) (bz : b.obj Z ⟶ W) (bY : b.obj C ⟶ U)
    (te : W ≅ V) (tf : U ⟶ T) (bq : W ⟶ U)
    (hm : m ≫ u = z ≫ q)
    (hF : tF.hom ≫ v = b.map u ≫ bY ≫ tf)
    (hE : tE.hom ≫ ve = b.map z ≫ bz ≫ te.hom)
    (hn : b.map q ≫ bY = bz ≫ bq) :
    tE.inv ≫ b.map m ≫ tF.hom ≫ v = ve ≫ te.inv ≫ bq ≫ tf := by
  have hi : tE.inv ≫ b.map z ≫ bz = ve ≫ te.inv := by
    apply (cancel_mono te.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [← hE, Iso.inv_hom_id_assoc]
  calc
    tE.inv ≫ b.map m ≫ tF.hom ≫ v =
        tE.inv ≫ b.map m ≫ b.map u ≫ bY ≫ tf := by rw [hF]
    _ = tE.inv ≫ b.map z ≫ bz ≫ bq ≫ tf := by
      rw [← b.map_comp_assoc, hm, b.map_comp, Category.assoc, reassoc_of% hn]
    _ = ve ≫ te.inv ≫ bq ≫ tf := by
      exact (reassoc_of% hi) (bq ≫ tf)

namespace AlgebraicGeometry.ProEtale
open Scheme PadicAlgCl

private lemma tensorComp_complex_fac
    (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    {E G : FiniteIntermediateField ℓ} (h : E ≤ G)
    (K : CochainComplex
      (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E)) ℤ) :
    (derivedExtendScalarsCompIso X ℓ h).hom.app (DerivedCategory.Q.obj K) ≫
      (coefficientComplexAlgClExtensionIso X ℓ E K).hom =
    (derivedExtendScalarsToPadicAlgCl X ℓ G).map
        (coefficientComplexExtensionIso X ℓ h K).hom ≫
      (coefficientComplexAlgClExtensionIso X ℓ G
        (((Mod.extendScalars (padicSubfieldRingObjMap X ℓ h)).mapHomologicalComplex
          (.up ℤ)).obj K)).hom ≫
      DerivedCategory.Q.map ((coefficientComplexTensorIso X ℓ h).hom.app K) := by
  have hh := Mod.exact_comparison_complex
    (A := Sheaf (ProEt.topology X) Ab.{u + 1})
    (R := padicSubfieldRingObj X ℓ E) (S := padicSubfieldRingObj X ℓ G)
    (T := padicAlgClRingObj X ℓ)
    (Mod.extendScalars (padicSubfieldRingObjMap X ℓ h))
    (Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ G))
    (Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ E))
    ((Mod.extendScalarsComp (padicSubfieldRingObjMap X ℓ h)
      (padicSubfieldRingObjToPadicAlgCl X ℓ G)).symm ≪≫
      Mod.extendScalarsIsoOfEq (padicSubfieldRingObjMap_comp_toPadicAlgCl X ℓ h)) K
  simpa only [derivedExtendScalarsCompIso, coefficientComplexAlgClExtensionIso,
    coefficientComplexExtensionIso, coefficientComplexTensorIso, coefficientTensorIso,
    CategoryTheory.Functor.mapHomologicalComplexCompIso, NatIso.mapHomologicalComplex,
    Iso.trans_hom, Iso.app_hom, CategoryTheory.Functor.map_comp, Category.assoc] using hh

/-- Exact localization preserves the coefficient tensor-comparison mate.

Source: `Adjunction.mapDerivedCategoryAdjunction_unit_app_fac`,
`Functor.mapDerivedCategoryCompIso_fac`, and `Functor.mapDerivedCategoryNatIso_fac`;
the derived comparison definitions in the coefficient construction of archived
`ModuleObject/Colimit/TwoColimit.lean`.
(auxiliary; not a blueprint node)

Proof: write the exact extension comparison as its left-derived-to-levelwise
isomorphism followed by mapDerivedCategoryFactors. The localized ordinary unit
is the derived unit followed by these factorizations for extension and
restriction; this follows from the unit factorization on the homotopy category
and naturality of quotientCompQhIso. Hence localizing an ordinary adjunction mate
agrees with taking the derived mate after these comparisons. Expand the
prescribed tensor comparison. Naturality cancels the exact-functor comparison
isomorphisms; mapDerivedCategoryCompIso_fac and mapDerivedCategoryNatIso_fac
identify its remaining factors with the localized ordinary tensor comparison.
Apply these identities to the finite adjunction's counit at the extended complex,
then to the algebraic-closure adjunction, and cancel inverse pairs. This yields
Q of the ordinary transposed map followed by the explicit vertex comparison.
The argument is for arbitrary complexes and uses no boundedness. -/
theorem coefficientComplex_derived_mate_transport
    (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    {E F G : FiniteIntermediateField ℓ} (he : E ≤ G) (hf : F ≤ G)
    (C : CochainComplex
      (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ F)) ℤ) :
    finiteCoefficientDerivedAlgClHomEquiv X ℓ E
      (DerivedCategory.Q.obj ((coefficientComplexStage X ℓ he hf).obj C)) _
      ((derivedExtendScalarsCompIso X ℓ he).inv.app
          (DerivedCategory.Q.obj ((coefficientComplexStage X ℓ he hf).obj C)) ≫
        (derivedExtendScalarsToPadicAlgCl X ℓ G).map
          ((finiteCoefficientDerivedHomEquiv X ℓ he
              (DerivedCategory.Q.obj ((coefficientComplexStage X ℓ he hf).obj C)) _).symm
            (coefficientComplexStageIso X ℓ he hf C).hom) ≫
        (derivedExtendScalarsCompIso X ℓ hf).hom.app (DerivedCategory.Q.obj C)) =
      DerivedCategory.Q.map (coefficientComplexTransposedMap X ℓ he hf C) ≫
        (coefficientComplexVertexIso X ℓ (E := E) C).hom := by
  let K := (coefficientComplexStage X ℓ he hf).obj C
  let Y := ((Mod.extendScalars (padicSubfieldRingObjMap X ℓ hf)).mapHomologicalComplex
    (.up ℤ)).obj C
  let U := finiteCoefficientDerivedRestriction X ℓ he
  let u := coefficientComplexExtensionIso X ℓ hf C
  let ue := coefficientComplexExtensionIso X ℓ he K
  let a := (Mod.extendRestrictAdjunction
    (padicSubfieldRingObjMap X ℓ he)).mapHomologicalComplex (.up ℤ)
  let ε : ((Mod.extendScalars (padicSubfieldRingObjMap X ℓ he)).mapHomologicalComplex
    (.up ℤ)).obj K ⟶ Y := a.counit.app Y
  let L := (derivedExtendScalarsSubfield X ℓ hf).obj (DerivedCategory.Q.obj C)
  have hm' : finiteCoefficientDerivedHomEquiv X ℓ he
      (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj Y)
      (ue.hom ≫ DerivedCategory.Q.map ε) =
        (Mod.comap (D := Sheaf (ProEt.topology X) Ab.{u + 1})
        (padicSubfieldRingObjMap X ℓ he)).mapDerivedCategoryFactors.inv.app Y := by
    exact Mod.derived_mate_counit (padicSubfieldRingObjMap X ℓ he) Y
  have hstage : (coefficientComplexStageIso X ℓ he hf C).hom ≫ U.map u.hom =
      (Mod.comap (D := Sheaf (ProEt.topology X) Ab.{u + 1})
        (padicSubfieldRingObjMap X ℓ he)).mapDerivedCategoryFactors.inv.app Y := by
    change ((Mod.comap (D := Sheaf (ProEt.topology X) Ab.{u + 1})
        (padicSubfieldRingObjMap X ℓ he)).mapDerivedCategoryFactors.inv.app
      Y ≫ U.map u.inv) ≫ U.map u.hom = _
    exact iso_map_cancel U _ u
  have hfinite : (finiteCoefficientDerivedHomEquiv X ℓ he
      (DerivedCategory.Q.obj K) L).symm
      (coefficientComplexStageIso X ℓ he hf C).hom ≫ u.hom =
        ue.hom ≫ DerivedCategory.Q.map ε := by
    exact adjoint_comparison_triangle (finiteCoefficientDerivedAdjunction X ℓ he)
      (coefficientComplexStageIso X ℓ he hf C) u
      (ue.hom ≫ DerivedCategory.Q.map ε) (hm'.trans hstage.symm)
  let b := derivedExtendScalarsToPadicAlgCl X ℓ G
  let Z := ((Mod.extendScalars (padicSubfieldRingObjMap X ℓ he)).mapHomologicalComplex
    (.up ℤ)).obj K
  let YΩ := ((Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ F)).mapHomologicalComplex
    (.up ℤ)).obj C
  let v := coefficientComplexAlgClExtensionIso X ℓ F C
  let ve := coefficientComplexAlgClExtensionIso X ℓ E K
  let bz := coefficientComplexAlgClExtensionIso X ℓ G Z
  let bY := coefficientComplexAlgClExtensionIso X ℓ G Y
  let te := (coefficientComplexTensorIso X ℓ he).app K
  let tf := (coefficientComplexTensorIso X ℓ hf).app C
  let m := (finiteCoefficientDerivedHomEquiv X ℓ he (DerivedCategory.Q.obj K) L).symm
    (coefficientComplexStageIso X ℓ he hf C).hom
  let sd := (derivedExtendScalarsCompIso X ℓ he).inv.app
      (DerivedCategory.Q.obj K) ≫ b.map m ≫
      (derivedExtendScalarsCompIso X ℓ hf).hom.app (DerivedCategory.Q.obj C)
  let sc := (coefficientComplexTensorIso X ℓ he).inv.app K ≫
    ((Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ G)).mapHomologicalComplex
      (.up ℤ)).map ε ≫ (coefficientComplexTensorIso X ℓ hf).hom.app C
  have hE := tensorComp_complex_fac X ℓ he K
  change (derivedExtendScalarsCompIso X ℓ he).hom.app
      (DerivedCategory.Q.obj K) ≫ ve.hom =
    b.map ue.hom ≫ bz.hom ≫ DerivedCategory.Q.map te.hom at hE
  have hF := tensorComp_complex_fac X ℓ hf C
  change (derivedExtendScalarsCompIso X ℓ hf).hom.app
      (DerivedCategory.Q.obj C) ≫ v.hom =
    b.map u.hom ≫ bY.hom ≫ DerivedCategory.Q.map tf.hom at hF
  have hn₀ := Mod.exact_comparison_naturality
    (A := Sheaf (ProEt.topology X) Ab.{u + 1})
    (R := padicSubfieldRingObj X ℓ G) (S := padicAlgClRingObj X ℓ)
    (Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ G)) ε
  have hn : b.map (DerivedCategory.Q.map ε) ≫ bY.hom =
      bz.hom ≫ DerivedCategory.Q.map
        (((Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ G)).mapHomologicalComplex
          (.up ℤ)).map ε) := by
    simpa only [b, bY, bz, Z, coefficientComplexAlgClExtensionIso,
      derivedExtendScalarsToPadicAlgCl, Iso.trans_hom, Iso.app_hom, Category.assoc] using hn₀
  have hs₀ := mate_transport_word b m u.hom ue.hom (DerivedCategory.Q.map ε)
    ((derivedExtendScalarsCompIso X ℓ he).app (DerivedCategory.Q.obj K))
    ((derivedExtendScalarsCompIso X ℓ hf).app (DerivedCategory.Q.obj C))
    v.hom ve.hom bz.hom bY.hom (DerivedCategory.Q.mapIso te)
    (DerivedCategory.Q.map tf.hom)
    (DerivedCategory.Q.map
      (((Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ G)).mapHomologicalComplex
        (.up ℤ)).map ε)) hfinite hF hE hn
  have hs : sd ≫ v.hom = ve.hom ≫ DerivedCategory.Q.map sc := by
    simpa only [sd, sc, te, tf, Iso.app_inv, Iso.app_hom,
      CategoryTheory.Functor.map_comp, CategoryTheory.Functor.mapIso_inv,
      Category.assoc] using hs₀
  have ho := Mod.derived_mate_complex (padicSubfieldRingObjToPadicAlgCl X ℓ E) K YΩ sc
  have houter : finiteCoefficientDerivedAlgClHomEquiv X ℓ E
      (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj YΩ)
      (ve.hom ≫ DerivedCategory.Q.map sc) =
        DerivedCategory.Q.map (coefficientComplexTransposedMap X ℓ he hf C) ≫
          (Mod.comap (D := Sheaf (ProEt.topology X) Ab.{u + 1})
        (padicSubfieldRingObjToPadicAlgCl X ℓ E)).mapDerivedCategoryFactors.inv.app
            YΩ := by
    change (finiteCoefficientDerivedAlgClAdjunction X ℓ E).homEquiv
      (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj YΩ)
      (ve.hom ≫ DerivedCategory.Q.map sc) =
        DerivedCategory.Q.map
          (((Mod.extendRestrictAdjunction
            (padicSubfieldRingObjToPadicAlgCl X ℓ E)).mapHomologicalComplex
              (.up ℤ)).homEquiv K YΩ sc) ≫ _ at ho
    have hc : coefficientComplexTransposedMap X ℓ he hf C =
        ((Mod.extendRestrictAdjunction
          (padicSubfieldRingObjToPadicAlgCl X ℓ E)).mapHomologicalComplex
            (.up ℤ)).homEquiv K YΩ sc := by
      unfold coefficientComplexTransposedMap
      rfl
    exact ho.trans (congrArg (fun f ↦ DerivedCategory.Q.map f ≫
      (Mod.comap (D := Sheaf (ProEt.topology X) Ab.{u + 1})
        (padicSubfieldRingObjToPadicAlgCl X ℓ E)).mapDerivedCategoryFactors.inv.app
        YΩ) hc.symm)
  have ho' : finiteCoefficientDerivedAlgClHomEquiv X ℓ E
      (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj YΩ) (sd ≫ v.hom) =
      DerivedCategory.Q.map (coefficientComplexTransposedMap X ℓ he hf C) ≫
        (Mod.comap (D := Sheaf (ProEt.topology X) Ab.{u + 1})
        (padicSubfieldRingObjToPadicAlgCl X ℓ E)).mapDerivedCategoryFactors.inv.app
          YΩ := by
    exact (congrArg (finiteCoefficientDerivedAlgClHomEquiv X ℓ E
      (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj YΩ)) hs).trans houter
  have hout := adjoint_comparison_target (finiteCoefficientDerivedAlgClAdjunction X ℓ E)
    sd v ((Mod.comap (D := Sheaf (ProEt.topology X) Ab.{u + 1})
        (padicSubfieldRingObjToPadicAlgCl X ℓ E)).mapDerivedCategoryFactors.app
      YΩ) (DerivedCategory.Q.map (coefficientComplexTransposedMap X ℓ he hf C)) ho'
  dsimp (config := { proj := false }) only [sd, b, m, v, K, YΩ, L] at hout
  simpa only
    [finiteCoefficientDerivedAlgClHomEquiv, coefficientComplexVertexIso,
    Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv, Category.assoc,
    CategoryTheory.Functor.mapIso_hom, CategoryTheory.Functor.mapIso_inv] using hout

end AlgebraicGeometry.ProEtale
