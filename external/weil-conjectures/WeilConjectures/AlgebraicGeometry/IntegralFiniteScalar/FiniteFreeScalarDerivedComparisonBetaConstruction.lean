/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralFiniteScalar.IntegralFiniteScalarModelDefinitions
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
import all WeilConjectures.CategoryTheory.ModuleObjects.KFlatScalarTower.InternalKFlatScalarTowerRealizationSupplement
import WeilConjectures.AlgebraicGeometry.IntegralFiniteScalar.FiniteFreeScalarDerivedComparisonAugmentation

/-! Existence of the normalized finite-free beta comparison.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.IntegralFiniteScalar
open CondensedRing

attribute [local irreducible] Functor.mapDerivedCategory
  Functor.leftDerivedFunctor Sheaf.monoidalCategory

section Generic

universe a v w b vb wb
variable {A : Type a} [Category.{v} A] [Abelian A] [MonoidalCategory A]
  [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [IsGrothendieckAbelian.{v} A] [Abelian.HasFunctorialFlatResolution A]
  [HasDerivedCategory.{w} A]

omit [Abelian.HasFunctorialFlatResolution A] [HasDerivedCategory A] in
private def singleTensorComparison (P : CochainComplex A ℤ) (B : A)
    (q : P ≅ (HomologicalComplex.single A (.up ℤ) 0).obj B)
    (F : A ⥤ A) [F.Additive] (κ : tensorLeft B ≅ F) :
    tensorLeft P ≅ F.mapHomologicalComplex (.up ℤ) :=
  (tensoringLeft (CochainComplex A ℤ)).mapIso q ≪≫
    CochainComplex.map₂HomologicalComplexObjSingleIso (curriedTensor A) B ≪≫
      NatIso.mapHomologicalComplex κ (.up ℤ)

omit [Abelian.HasFunctorialFlatResolution A] [HasDerivedCategory A] in
private lemma singleTensorComparison_summand (P : CochainComplex A ℤ) (B : A)
    (q : P ≅ (HomologicalComplex.single A (.up ℤ) 0).obj B)
    (F : A ⥤ A) [F.Additive] (κ : tensorLeft B ≅ F)
    (C : CochainComplex A ℤ) (n : ℤ) :
    HomologicalComplex.ιTensorObj P C 0 n n (zero_add n) ≫
        ((singleTensorComparison P B q F κ).hom.app C).f n =
      (q.hom.f 0 ≫ (HomologicalComplex.singleObjXSelf (.up ℤ) 0 B).hom) ▷ C.X n ≫
        κ.hom.app (C.X n) := by
  let e := CochainComplex.mapBifunctorSingle₁Iso (curriedTensor A) B C
  have hs : HomologicalComplex.ιTensorObj
      ((HomologicalComplex.single A (.up ℤ) 0).obj B) C 0 n n (zero_add n) ≫
        e.hom.f n = (HomologicalComplex.singleObjXSelf (.up ℤ) 0 B).hom ▷ C.X n := by
    have hi := congrArg (fun f ↦ f.f n) e.inv_hom_id
    simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f,
      e, CochainComplex.mapBifunctorSingle₁Iso_inv_f] at hi
    change (((HomologicalComplex.singleObjXSelf (.up ℤ) 0 B).inv ▷ C.X n) ≫
      HomologicalComplex.ιTensorObj _ C 0 n n (zero_add n)) ≫ e.hom.f n = 𝟙 _ at hi
    apply (cancel_epi
      ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 B).inv ▷ C.X n)).1
    rw [← Category.assoc, hi]
    simp only [← comp_whiskerRight, Iso.inv_hom_id, id_whiskerRight]
  change _ ≫ ((q.hom ▷ C) ≫ e.hom ≫
    (NatIso.mapHomologicalComplex κ (.up ℤ)).hom.app C).f n = _
  simp only [HomologicalComplex.comp_f]
  rw [← Category.assoc]
  erw [HomologicalComplex.ι_mapBifunctorMap]
  simp only [HomologicalComplex.id_f, CategoryTheory.Functor.map_id,
    Category.id_comp, Category.assoc]
  rw [reassoc_of% hs]
  change (q.hom.f 0 ▷ C.X n) ≫
    ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 B).hom ▷ C.X n) ≫ κ.hom.app (C.X n) = _
  rw [← comp_whiskerRight_assoc]

private lemma tensorCounit_isIso (B C : CochainComplex A ℤ)
    (hC : (HomologicalComplex.quasiIso A (.up ℤ)).kFlat C) :
    IsIso (Functor.LaxMonoidal.μ DerivedCategory.Q B C) := by
  have hm : IsIso (Functor.LaxMonoidal.μ DerivedCategory.Qh
      ((HomotopyCategory.quotient A (.up ℤ)).obj B)
      ((HomotopyCategory.quotient A (.up ℤ)).obj C)) :=
    DerivedMonoidal.isIso_counit_app_app_of_kFlat_right DerivedCategory.Qh
      (HomotopyCategory.quasiIso A (.up ℤ)) _ _
      ((HomotopyCategory.kFlat_quotient_obj_iff C).2 hC)
  change IsIso ((_ ⊗ₘ _) ≫ (Functor.LaxMonoidal.μ DerivedCategory.Qh _ _ ≫
    DerivedCategory.Qh.map _) ≫ _)
  infer_instance

private def tensorCounit (B : CochainComplex A ℤ) :
    DerivedCategory.Q ⋙ tensorLeft (DerivedCategory.Q.obj B) ⟶
      tensorLeft B ⋙ DerivedCategory.Q where
  app C := Functor.LaxMonoidal.μ DerivedCategory.Q B C
  naturality _C _C' f := Functor.LaxMonoidal.μ_natural_right _ B f

private lemma descendTensorComparison
    (F G : DerivedCategory A ⥤ DerivedCategory A)
    (H : CochainComplex A ℤ ⥤ DerivedCategory A)
    (v : DerivedCategory.Q ⋙ F ⟶ H) (w : DerivedCategory.Q ⋙ G ⟶ H)
    (hv : ∀ C, (HomologicalComplex.quasiIso A (.up ℤ)).kFlat C → IsIso (v.app C))
    (hw : ∀ C, (HomologicalComplex.quasiIso A (.up ℤ)).kFlat C → IsIso (w.app C)) :
    ∃ e : F ≅ G, ∀ C, (HomologicalComplex.quasiIso A (.up ℤ)).kFlat C →
      e.hom.app (DerivedCategory.Q.obj C) ≫ w.app C = v.app C := by
  let I := CochainComplex.ιKFlat A
  let L := I ⋙ DerivedCategory.Q
  have : L.IsLocalization (HomologicalComplex.quasiIso A (.up ℤ)).WKFlat :=
    inferInstanceAs (((HomologicalComplex.quasiIso A
      (.up ℤ)).localizerMorphismKFlat.functor ⋙ DerivedCategory.Q).IsLocalization _)
  let v' : L ⋙ F ⟶ I ⋙ H := Functor.whiskerLeft I v
  let w' : L ⋙ G ⟶ I ⋙ H := Functor.whiskerLeft I w
  have : IsIso v' := by
    rw [NatTrans.isIso_iff_isIso_app]
    exact fun C ↦ hv C.obj C.property
  have : IsIso w' := by
    rw [NatTrans.isIso_iff_isIso_app]
    exact fun C ↦ hw C.obj C.property
  let ff := Localization.fullyFaithfulWhiskeringLeft L
    (HomologicalComplex.quasiIso A (.up ℤ)).WKFlat (DerivedCategory A)
  let e : F ≅ G := ff.preimageIso (asIso v' ≪≫ (asIso w').symm)
  refine ⟨e, ?_⟩
  intro C hC
  have he := congrArg (fun f ↦ f.app ⟨C, hC⟩)
    (ff.map_preimage (asIso v' ≪≫ (asIso w').symm).hom)
  change e.hom.app (DerivedCategory.Q.obj C) = v.app C ≫ (asIso w').inv.app ⟨C, hC⟩
    at he
  rw [he, Category.assoc]
  change v.app C ≫ ((asIso w').inv.app ⟨C, hC⟩ ≫
    (asIso w').hom.app ⟨C, hC⟩) = v.app C
  rw [(asIso w').inv_hom_id_app]
  exact Category.comp_id (v.app C)

private lemma cochainCounit_eq
    {D : Type b} [Category.{vb} D] [Abelian D] [HasDerivedCategory.{wb} D]
    (F : A ⥤ D) [F.Additive] [F.PreservesKFlatQuasiIso] (C : CochainComplex A ℤ) :
    F.leftDerivedFunctor.map ((DerivedCategory.quotientCompQhIso A).inv.app C) ≫
      F.leftDerivedFunctorCounit.app ((HomotopyCategory.quotient A (.up ℤ)).obj C) ≫
      (DerivedCategory.quotientCompQhIso D).hom.app _ =
        F.leftDerivedFunctorCounit.app ((HomotopyCategory.quotient A (.up ℤ)).obj C) := by
  dsimp only [DerivedCategory.quotientCompQhIso,
    HomologicalComplexUpToQuasiIso.quotientCompQhIso, Quotient.lift.isLift_inv,
    Quotient.lift.isLift_hom]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]

end Generic

private abbrev betaMap {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ') (Z : Scheme.{u}) :=
  coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom Z

private abbrev betaCoefficient {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    (Z : Scheme.{u}) :=
  (Mod.comap (betaMap a Z)).obj (Mod.regular (condensedRingObj Λ'.X Z))

private def betaOrdinary {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ') (Z : Scheme.{u}) :
    tensorLeft (betaCoefficient a Z) ≅
      Mod.extendScalars (betaMap a Z) ⋙ Mod.comap (betaMap a Z) :=
  (Mod.KFlatScalarTower.extendTensorNatIso (betaMap a Z)).symm

private lemma betaOrdinary_hom {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ') (Z : Scheme.{u})
    (M : ModuleRingedComparison.internalModules Λ.X Z) :
    ((betaOrdinary a Z).app M).hom.hom =
      (Mod.extendForgetTensorObjIso (betaMap a Z) M).inv := by
  rfl

attribute [local irreducible] betaOrdinary

private def betaTargetIso {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    (S : ShortComplex (PointModules Λ))
    (t : S.X₃ ≅ (Mod.comap a.hom.hom).obj (Mod.regular Λ'.X)) (Z : Scheme.{u}) :
    target Λ S Z ≅ (HomologicalComplex.single _ (.up ℤ) 0).obj (betaCoefficient a Z) :=
  (HomologicalComplex.singleMapHomologicalComplex (pointPull Λ Z) (.up ℤ) 0).app S.X₃ ≪≫
    (HomologicalComplex.single _ (.up ℤ) 0).mapIso
      ((pointPull Λ Z).mapIso t ≪≫ coefficientModuleIso a Z)

private lemma betaTargetIso_zero {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    (S : ShortComplex (PointModules Λ))
    (t : S.X₃ ≅ (Mod.comap a.hom.hom).obj (Mod.regular Λ'.X)) (Z : Scheme.{u}) :
    (betaTargetIso a S t Z).hom.f 0 ≫
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (betaCoefficient a Z)).hom =
        (targetZeroIso a S t Z).hom := by
  simp [betaTargetIso, targetZeroIso, Iso.trans_hom, HomologicalComplex.comp_f,
    HomologicalComplex.single_map_f_self]

attribute [local irreducible] betaTargetIso

private def betaTotalNatIso {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    (S : ShortComplex (PointModules Λ))
    (t : S.X₃ ≅ (Mod.comap a.hom.hom).obj (Mod.regular Λ'.X)) (Z : Scheme.{u}) :
    tensorLeft (target Λ S Z) ≅
      (Mod.extendScalars (betaMap a Z) ⋙ Mod.comap (betaMap a Z)).mapHomologicalComplex
        (.up ℤ) :=
  singleTensorComparison (target Λ S Z) (betaCoefficient a Z) (betaTargetIso a S t Z)
    _ (betaOrdinary a Z)

private lemma betaTotalIso_summand {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    (S : ShortComplex (PointModules Λ))
    (t : S.X₃ ≅ (Mod.comap a.hom.hom).obj (Mod.regular Λ'.X)) (Z : Scheme.{u})
    (C : CochainComplex (ModuleRingedComparison.internalModules Λ.X Z) ℤ) (n : ℤ) :
    HomologicalComplex.ιTensorObj (target Λ S Z) C 0 n n (zero_add n) ≫
        ((betaTotalNatIso a S t Z).app C).hom.f n =
      ((targetZeroIso a S t Z).hom ⊗ₘ 𝟙 (C.X n)) ≫
        ((betaOrdinary a Z).app (C.X n)).hom := by
  have h := singleTensorComparison_summand (target Λ S Z) (betaCoefficient a Z)
    (betaTargetIso a S t Z) _ (betaOrdinary a Z) C n
  rw [betaTargetIso_zero] at h
  simpa only [betaTotalNatIso, tensorHom_id, Iso.app_hom] using h

private lemma betaScalarCounit_eq {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    (Z : Scheme.{u}) (C : CochainComplex (ModuleRingedComparison.internalModules Λ.X Z) ℤ) :
    scalarCounit a Z C = (Mod.KFlatScalarTower.computationCounit (betaMap a Z)).app C := by
  simp [scalarCounit, Mod.KFlatScalarTower.computationCounit,
    Functor.mapHomotopyCategoryFactors_hom_app, scalarSixChange, scalarSixAdjunctionLeft,
    betaMap, HomotopyCategory.quotient_obj_as]

private def betaScalarCounit {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ') (Z : Scheme.{u}) :
    DerivedCategory.Q ⋙ scalarSixChange a Z ⟶
      (Mod.extendScalars (betaMap a Z)).mapHomologicalComplex (.up ℤ) ⋙
        DerivedCategory.Q where
  app C := scalarCounit a Z C
  naturality C C' f := by
    change (scalarSixChange a Z).map (DerivedCategory.Q.map f) ≫ scalarCounit a Z C' =
      scalarCounit a Z C ≫ DerivedCategory.Q.map _
    rw [betaScalarCounit_eq, betaScalarCounit_eq]
    exact (Mod.KFlatScalarTower.computationCounit (betaMap a Z)).naturality f

private lemma betaScalarCounit_isIso {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    (Z : Scheme.{u}) (C : CochainComplex (ModuleRingedComparison.internalModules Λ.X Z) ℤ)
    (hC : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat C) :
    IsIso (scalarCounit a Z C) := by
  have := (Mod.extendScalars (betaMap a Z)).isIso_leftDerivedFunctorCounit_app_of_kFlat C hC
  dsimp only [scalarCounit]
  infer_instance

private def betaRestrictedCounit {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    (Z : Scheme.{u}) :
    DerivedCategory.Q ⋙ (scalarSixChange a Z ⋙ restriction a Z) ⟶
      (Mod.extendScalars (betaMap a Z)).mapHomologicalComplex (.up ℤ) ⋙
        (Mod.comap (betaMap a Z)).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
  Functor.whiskerRight (betaScalarCounit a Z) (restriction a Z) ≫
    Functor.whiskerLeft ((Mod.extendScalars (betaMap a Z)).mapHomologicalComplex (.up ℤ))
      (Mod.comap (betaMap a Z)).mapDerivedCategoryFactors.hom

/--
Choose flat-term K-flat representatives, apply the restricted tensor
identification, and descend the augmentation comparison. This is the existence and
ordinary normalization part of the beta construction.
-/
theorem finiteFreeScalarDerivedComparison_beta_construction
    (D : ScalarSixPullbackData.{u}) {Λ Λ' : ScalarSixRing.{u}}
    (a : Λ ⟶ Λ') (S : ShortComplex (PointModules Λ))
    (t : S.X₃ ≅ (Mod.comap a.hom.hom).obj (Mod.regular Λ'.X))
    (hS : S.ShortExact) (r : ℕ)
    (e₁ : S.X₁ ≅ biproduct (fun _ : Fin r ↦ Mod.regular Λ.X))
    (e₂ : S.X₂ ≅ biproduct (fun _ : Fin r ↦ Mod.regular Λ.X)) :
    ∃ β : ∀ Z : Scheme.{u}, tensorLeft (DerivedCategory.Q.obj (complex Λ S Z)) ≅
        scalarSixChange a Z ⋙ restriction a Z,
      ∀ Z, AugmentationNormalized a S t Z (β Z) := by
  classical
  have hz (Z : Scheme.{u}) : ∃ β : tensorLeft
      (DerivedCategory.Q.obj (complex Λ S Z)) ≅ scalarSixChange a Z ⋙ restriction a Z,
      AugmentationNormalized a S t Z β := by
    have haug : QuasiIso (augmentation Λ S Z) :=
      finiteFreeScalarDerivedComparison_augmentation D a S t hS r e₁ e₂ Z
    let H := (Mod.extendScalars (betaMap a Z)).mapHomologicalComplex (.up ℤ) ⋙
      (Mod.comap (betaMap a Z)).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q
    let v : DerivedCategory.Q ⋙ tensorLeft (DerivedCategory.Q.obj (complex Λ S Z)) ⟶ H :=
      tensorCounit (complex Λ S Z) ≫
        Functor.whiskerRight ((tensoringLeft _).map (augmentation Λ S Z)) DerivedCategory.Q ≫
        Functor.whiskerRight (betaTotalNatIso a S t Z).hom DerivedCategory.Q
    have hv C (hC : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat C) :
        IsIso (v.app C) := by
      have : IsIso (Functor.LaxMonoidal.μ DerivedCategory.Q (target Λ S Z) C) :=
        tensorCounit_isIso (target Λ S Z) C hC
      dsimp only [v, NatTrans.comp_app, Functor.whiskerRight_app, tensorCounit]
      change IsIso (Functor.LaxMonoidal.μ DerivedCategory.Q (complex Λ S Z) C ≫
        DerivedCategory.Q.map (augmentation Λ S Z ▷ C) ≫
        DerivedCategory.Q.map ((betaTotalNatIso a S t Z).hom.app C))
      erw [← Functor.LaxMonoidal.μ_natural_left_assoc]
      infer_instance
    have hw C (hC : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat C) :
        IsIso ((betaRestrictedCounit a Z).app C) := by
      have := betaScalarCounit_isIso a Z C hC
      dsimp only [betaRestrictedCounit, betaScalarCounit, NatTrans.comp_app,
        Functor.whiskerRight_app, Functor.whiskerLeft_app]
      infer_instance
    obtain ⟨β, hβ⟩ := descendTensorComparison _ _ H v (betaRestrictedCounit a Z) hv hw
    refine ⟨β, fun M ↦ (betaOrdinary a Z).app M, ?_, ?_⟩
    · intro M
      exact betaOrdinary_hom a Z M
    · intro C hC
      refine ⟨(betaTotalNatIso a S t Z).app C, betaTotalIso_summand a S t Z C, ?_⟩
      exact hβ C hC
  choose β hβ using hz
  exact ⟨β, hβ⟩

end AlgebraicGeometry.ProEtale.IntegralFiniteScalar
