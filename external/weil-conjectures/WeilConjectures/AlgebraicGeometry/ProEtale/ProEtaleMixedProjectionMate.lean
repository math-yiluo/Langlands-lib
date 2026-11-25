/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback

public import WeilConjectures.AlgebraicGeometry.ProEtale.Projection.ProEtaleProjectionFormulaArrows
public import WeilConjectures.CategoryTheory.Projection.ProjectionFormulaBaseChangeNaturality
import all Mathlib.CategoryTheory.Limits.HasLimits
import all WeilConjectures.Algebra.Homology.ProperBaseChange.KFlatResolutionGeneral
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses

/-! # Computing the projection mate on mixed tensor representatives

## References

* Stacks Project, Cohomology on Sites, Tags 07A4, 07A6 and 0B56
-/

@[expose] public noncomputable section

set_option autoImplicit false
-- Avoid replaying the representative transport proof for tactic linting.
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v u' v' uA vA uB vB wA wB

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem quotient_obj
    {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
    (I : CochainComplex A ℤ) :
    DerivedCategory.Qh.obj ((HomotopyCategory.quotient A (.up ℤ)).obj I) =
      DerivedCategory.Q.obj I := rfl

private theorem cochain_counit
    {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
    [Abelian.HasKInjectiveResolutions B]
    (L : A ⥤ B) (V : B ⥤ A) [L.Additive] [V.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (am : L ⊣ V) (I : CochainComplex B ℤ) :
    L.mapDerivedCategory.map (V.rightDerivedFunctorUnit.app
        ((HomotopyCategory.quotient B (.up ℤ)).obj I)) ≫
      am.mapDerivedCategoryRightDerivedAdjunction.counit.app (DerivedCategory.Q.obj I) =
      L.mapDerivedCategoryFactors.hom.app ((V.mapHomologicalComplex (.up ℤ)).obj I) ≫
        DerivedCategory.Q.map ((am.mapHomologicalComplex (.up ℤ)).counit.app I) := by
  have hh := (am.mapHomotopyCategory (.up ℤ)).derivedε_fac_app
    (HomotopyCategory.quasiIso B (.up ℤ)) L.mapDerivedCategoryFactorsh.hom
    V.rightDerivedFunctorUnit ((HomotopyCategory.quotient B (.up ℤ)).obj I)
  change L.mapDerivedCategory.map _ ≫
    am.mapDerivedCategoryRightDerivedAdjunction.counit.app _ =
    L.mapDerivedCategoryFactorsh.hom.app
      ((HomotopyCategory.quotient A (.up ℤ)).obj
        ((V.mapHomologicalComplex (.up ℤ)).obj I)) ≫ _ at hh
  simp only [Functor.mapDerivedCategoryFactorsh_hom_app,
    Adjunction.mapHomotopyCategory_counit_app_quotient,
    Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift_inv,
    DerivedCategory.quotientCompQhIso, HomologicalComplexUpToQuasiIso.quotientCompQhIso,
    Category.assoc, Quotient.lift.isLift_hom] at hh
  erw [L.mapDerivedCategory.map_id] at hh
  erw [Category.id_comp] at hh
  erw [(DerivedCategory.Qh (C := B)).map_id] at hh
  erw [Category.id_comp] at hh
  erw [Category.id_comp] at hh
  exact hh

attribute [local irreducible] SheafOfModules.monoidalClosed_kfg

private theorem acyclic_of_quasiIso_preservation
    {M : Type uA} [Category.{vA} M] [Abelian M]
    (U : CochainComplex M ℤ ⥤ CochainComplex M ℤ) [U.PreservesZeroMorphisms]
    (hU : ∀ {Z Z' : CochainComplex M ℤ} (p : Z ⟶ Z'),
      QuasiIso p → QuasiIso (U.map p))
    (Z : CochainComplex M ℤ) (hZ : Z.Acyclic) : (U.obj Z).Acyclic := by
  let : Zero (CochainComplex M ℤ) := HasZeroObject.zero' _
  have hz : QuasiIso (0 : (0 : CochainComplex M ℤ) ⟶ Z) := by
    rw [quasiIso_iff]
    intro i
    exact (quasiIsoAt_iff_exactAt _ i
      ((HomologicalComplex.acyclic_of_isZero _ (isZero_zero _)) i)).2 (hZ i)
  have hmap : QuasiIso (U.map (0 : (0 : CochainComplex M ℤ) ⟶ Z)) := hU _ hz
  have htzero : (U.obj (0 : CochainComplex M ℤ)).Acyclic :=
    HomologicalComplex.acyclic_of_isZero _ (U.map_isZero (isZero_zero _))
  exact fun i ↦ (exactAt_iff_of_quasiIsoAt
    (U.map (0 : (0 : CochainComplex M ℤ) ⟶ Z)) i).1 (htzero i)

-- The tensor representatives involve several nested localization comparisons.
private theorem flat_resolution_functor
    (T : Scheme.{u}) (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) :
    ∃ D : CochainComplex (proEtaleRingModules T R) ℤ ⥤
        CochainComplex (proEtaleRingModules T R) ℤ,
      ∃ q : D ⟶ 𝟭 _, ∀ K, proEtaleFlatRepresentatives T R (D.obj K) ∧
        QuasiIso (q.app K) := by
  classical
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  let := SheafOfModules.monoidalClosed_kfg (R := R)
  let := SheafOfModules.monoidalPreadditive_kfg R
  let := SheafOfModules.isGrothendieckAbelian_kfg R
  let := SheafOfModules.hasFunctorialFlatResolution_kfg R
  let M := proEtaleRingModules T R
  have : ∀ X₁ X₂ : GradedObject ℤ M, GradedObject.HasTensor X₁ X₂ := by
    infer_instance
  have : ∀ X₁ X₂ X₃ : GradedObject ℤ M,
      GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃ := by infer_instance
  have : ∀ X₁ X₂ X₃ : GradedObject ℤ M,
      GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃ := by infer_instance
  have : ∀ X₁ X₂ X₃ X₄ : GradedObject ℤ M,
      GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄ := by infer_instance
  let : Zero (CochainComplex M ℤ) := HasZeroObject.zero' (CochainComplex M ℤ)
  let Λ := (Classical.arbitrary (Abelian.LeftResolution
    (ObjectProperty.flat.ι : _ ⥤ M))).reduced
  have hι : (ObjectProperty.flat.ι : _ ⥤ M).essImage ≤ ObjectProperty.flat :=
    ObjectProperty.flat.essImage_ι_le
  have hres (K : CochainComplex M ℤ) :
      proEtaleFlatRepresentatives T R (Λ.resolutionFunctor.obj K) := by
    have hk := Λ.kFlat_resolutionFunctor_obj hι K
    have hflat (n : ℤ) : ObjectProperty.flat ((Λ.resolutionFunctor.obj K).X n) := by
      have := CochainComplex.closedUnderColimitsOfShape_flat M ℤ
      let c := Λ.colimitOfShapeResolutionFunctorObj K
      exact ObjectProperty.prop_of_isColimit _
        (isColimitOfPreserves (HomologicalComplex.eval M (.up ℤ) n) c.isColimit)
        (fun i ↦ hι _ ((c.prop_diag_obj i).1 n))
    refine ⟨?_, fun n ↦ (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso R _).symm (hflat n).2⟩
    let U := ((proEtaleOrdinaryTensor T R).map₂HomologicalComplex
      (.up ℤ) (.up ℤ) (.up ℤ)).flip.obj (Λ.resolutionFunctor.obj K)
    exact acyclic_of_quasiIso_preservation (M := M) U (fun p hp ↦ hk.2 p hp)
  exact ⟨Λ.resolutionFunctor, Λ.resolutionNatTrans,
    fun K ↦ ⟨hres K, inferInstance⟩⟩

private theorem mixed_naturality_generic
    {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    (Q : C ⥤ D) (T : D × D ⥤ D) (U : C ⥤ C) (F : D)
    (Z : ∀ A : C, T.obj (Q.obj A, F) ≅ Q.obj (U.obj A))
    (R : C ⥤ C) (q : R ⟶ 𝟭 C)
    (r : ∀ A : C, T.obj (Q.obj (R.obj A), F) ⟶ Q.obj (U.obj (R.obj A)))
    (hn : ∀ {A B : C} (f : A ⟶ B),
      T.map (Prod.mkHom (Q.map (R.map f)) (𝟙 F)) ≫ r B =
        r A ≫ Q.map (U.map (R.map f)))
    (hz : ∀ A, T.map (Prod.mkHom (Q.map (q.app A)) (𝟙 F)) ≫ (Z A).hom =
      r A ≫ Q.map (U.map (q.app A)))
    (hq : ∀ A, IsIso (Q.map (q.app A))) {A B : C} (f : A ⟶ B) :
    T.map (Prod.mkHom (Q.map f) (𝟙 F)) ≫ (Z B).hom =
      (Z A).hom ≫ Q.map (U.map f) := by
  have : IsIso (Q.map (q.app A)) := hq A
  have : IsIso (Prod.mkHom (Q.map (q.app A)) (𝟙 F)) :=
    (Iso.prod (asIso (Q.map (q.app A))) (Iso.refl F)).isIso_hom
  apply (cancel_epi (T.map (Prod.mkHom (Q.map (q.app A)) (𝟙 F)))).mp
  have heq : T.map (Prod.mkHom (Q.map (q.app A)) (𝟙 F)) ≫
      T.map (Prod.mkHom (Q.map f) (𝟙 F)) =
    T.map (Prod.mkHom (Q.map (R.map f)) (𝟙 F)) ≫
      T.map (Prod.mkHom (Q.map (q.app B)) (𝟙 F)) := by
    simp only [← T.map_comp, prod_comp, Category.id_comp, ← Q.map_comp]
    rw [q.naturality f]
    rfl
  rw [← Category.assoc, heq, Category.assoc, hz B,
    ← Category.assoc, hn f, Category.assoc, ← Category.assoc
      (T.map _) (Z A).hom, hz A, Category.assoc]
  congr 1
  simp only [← Q.map_comp, ← U.map_comp]
  rw [q.naturality f]
  rfl

private theorem mixed_normalization (T : AlgebraicGeometry.Scheme.{u})
    (R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology T) CommRingCat.{u + 1})
    (a : ProEtaleTensorModel T R)
    (A F P : CochainComplex (proEtaleRingModules T R) ℤ)
    (hf : proEtaleFlatRepresentatives T R F)
    (hp : proEtaleFlatRepresentatives T R P) (p : P ⟶ A) (hq : QuasiIso p) :
    a.tensor.map (Prod.mkHom (DerivedCategory.Q.map p) (𝟙 (DerivedCategory.Q.obj F))) ≫
        (proEtaleMixedTensor R a A F hf).hom =
      a.representative.inv.app (⟨P, hp⟩, ⟨F, hf⟩) ≫
        DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap p (𝟙 F)
          (proEtaleOrdinaryTensor T R) (.up ℤ)) :=
  (proEtaleMixedTensor_existsUnique R a A F hf).exists.choose_spec P hp p hq

private def representativeInv
    (T : Scheme.{u}) (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    (a : ProEtaleTensorModel T R)
    (P F : CochainComplex (proEtaleRingModules T R) ℤ)
    (hP : proEtaleFlatRepresentatives T R P) (hF : proEtaleFlatRepresentatives T R F) :
    a.tensor.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj F) ⟶
      DerivedCategory.Q.obj (CochainComplex.mapBifunctor P F (proEtaleOrdinaryTensor T R)) :=
  a.representative.inv.app (⟨P, hP⟩, ⟨F, hF⟩)

private theorem representativeInv_eq
    (T : Scheme.{u}) (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    (a : ProEtaleTensorModel T R)
    (P F : CochainComplex (proEtaleRingModules T R) ℤ)
    (hP : proEtaleFlatRepresentatives T R P) (hF : proEtaleFlatRepresentatives T R F) :
    a.representative.inv.app (⟨P, hP⟩, ⟨F, hF⟩) = representativeInv T R a P F hP hF := rfl

attribute [local irreducible] representativeInv

private theorem tensor_comparison_normalization
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)
    (a : ProEtaleTensorModel Y R) (b : ProEtaleTensorModel X S)
    (P F : CochainComplex (proEtaleRingModules Y R) ℤ)
    (hP : proEtaleFlatRepresentatives Y R P) (hF : proEtaleFlatRepresentatives Y R F)
    (hLP : proEtaleFlatRepresentatives X S
      (((proEtaleRingModulePullback f R S c).mapHomologicalComplex (.up ℤ)).obj P))
    (hLF : proEtaleFlatRepresentatives X S
      (((proEtaleRingModulePullback f R S c).mapHomologicalComplex (.up ℤ)).obj F)) :
    (proEtaleRingDerivedPullback f R S c).map
        (a.representative.hom.app (⟨P, hP⟩, ⟨F, hF⟩)) ≫
      (proEtaleCanonicalTensorComparison f R S c a b).hom.app
        (DerivedCategory.Q.obj P, DerivedCategory.Q.obj F) ≫
      b.tensor.map (Prod.mkHom
        ((proEtaleRingDerivedPullbackFactors f R S c).hom.app P)
        ((proEtaleRingDerivedPullbackFactors f R S c).hom.app F)) =
    (proEtaleRingDerivedPullbackFactors f R S c).hom.app
        (CochainComplex.mapBifunctor P F (proEtaleOrdinaryTensor Y R)) ≫
      (DerivedCategory.Q.mapIso (proEtaleTensorPullbackTotalIso f R S c P F)).inv ≫
      b.representative.hom.app
        (⟨_, hLP⟩, ⟨_, hLF⟩) := by
  obtain ⟨_, _, h⟩ :=
    (proEtaleCanonicalTensorPullback f R S c a b).2.exists.choose_spec P F hP hF
  exact h

attribute [local irreducible] proEtaleCanonicalTensorComparison

attribute [local irreducible] SheafOfModules.monoidalCategory proEtaleMixedTensor

-- Naturality of the uniquely specified tensor comparisons.
private theorem mixed_naturality
    (T : Scheme.{u}) (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    (a : ProEtaleTensorModel T R)
    (A B F : CochainComplex (proEtaleRingModules T R) ℤ)
    (hf : proEtaleFlatRepresentatives T R F) (f : A ⟶ B) :
    a.tensor.map (Prod.mkHom (DerivedCategory.Q.{u + 2}.map f)
      (𝟙 (DerivedCategory.Q.{u + 2}.obj F))) ≫
        (proEtaleMixedTensor R a B F hf).hom =
      (proEtaleMixedTensor R a A F hf).hom ≫
        DerivedCategory.Q.{u + 2}.map (HomologicalComplex.mapBifunctorMap f (𝟙 F)
          (proEtaleOrdinaryTensor T R) (.up ℤ)) := by
  classical
  obtain ⟨D, q, hres⟩ := flat_resolution_functor T R
  let U := ((proEtaleOrdinaryTensor T R).map₂HomologicalComplex
    (.up ℤ) (.up ℤ) (.up ℤ)).flip.obj F
  let r (A : CochainComplex (proEtaleRingModules T R) ℤ) :=
    a.representative.inv.app (⟨D.obj A, (hres A).1⟩, ⟨F, hf⟩)
  have hn {A B : CochainComplex (proEtaleRingModules T R) ℤ} (f : A ⟶ B) :
      a.tensor.map (Prod.mkHom (DerivedCategory.Q.map (D.map f))
        (𝟙 (DerivedCategory.Q.obj F))) ≫ r B =
      r A ≫ DerivedCategory.Q.map (U.map (D.map f)) := by
    have hh := a.representative.inv.naturality
      (Prod.mkHom (ObjectProperty.homMk
        (X := ⟨_, (hres A).1⟩) (Y := ⟨_, (hres B).1⟩) (D.map f))
        (𝟙 (⟨F, hf⟩ : (proEtaleFlatRepresentatives T R).FullSubcategory)))
    simp only [Functor.comp_map, Functor.prod_map, Functor.prod_obj,
      ObjectProperty.ι_obj, ObjectProperty.ι_map, ObjectProperty.homMk_hom,
      ObjectProperty.FullSubcategory.id_hom, Functor.uncurry_obj_map] at hh
    erw [DerivedCategory.Q.map_id F,
      (((proEtaleOrdinaryTensor T R).map₂HomologicalComplex
        (.up ℤ) (.up ℤ) (.up ℤ)).obj (D.obj B)).map_id F,
      Category.comp_id] at hh
    exact hh
  have hz (A : CochainComplex (proEtaleRingModules T R) ℤ) :
      a.tensor.map (Prod.mkHom (DerivedCategory.Q.map (q.app A))
        (𝟙 (DerivedCategory.Q.obj F))) ≫ (proEtaleMixedTensor R a A F hf).hom =
      r A ≫ DerivedCategory.Q.map (U.map (q.app A)) := by
    have hh := mixed_normalization T R a A F (D.obj A) hf
      (hres A).1 (q.app A) (hres A).2
    simpa only [U, r, Functor.id_obj, HomologicalComplex.mapBifunctorMap,
      Functor.flip_obj_map,
      Functor.map₂HomologicalComplex_map_app, Functor.map_id, Category.comp_id] using hh
  have hq (A : CochainComplex (proEtaleRingModules T R) ℤ) :
      IsIso (DerivedCategory.Q.map (q.app A)) := by
    have : QuasiIso (q.app A) := (hres A).2
    infer_instance
  have hh := mixed_naturality_generic DerivedCategory.Q a.tensor U
    (DerivedCategory.Q.obj F) (fun A ↦ proEtaleMixedTensor R a A F hf) D q r
    hn hz hq f
  simpa only [U, HomologicalComplex.mapBifunctorMap, Functor.flip_obj_map,
    Functor.map₂HomologicalComplex_map_app, Functor.map_id, Category.comp_id] using hh

private theorem projection_counit
    {C : Type uA} [Category.{vA} C] {D : Type uB} [Category.{vB} D]
    (L : C ⥤ D) (R : D ⥤ C) (adj : L ⊣ R)
    (T : C × C ⥤ C) (U : D × D ⥤ D)
    (b : T ⋙ L ≅ L.prod L ⋙ U) (I : D) (F : C) :
    L.map (derivedProjectionFormulaMate L R adj T U b I F) ≫
        adj.counit.app (U.obj (I, L.obj F)) =
      b.hom.app (R.obj I, F) ≫
        U.map (Prod.mkHom (adj.counit.app I) (𝟙 (L.obj F))) := by
  have h := adj.map_rightAdjointProjectionMap_app_app_comp_counit
    (T_C := Functor.curry.obj U) (T_D := Functor.curry.obj T)
    (Functor.curry.map b.hom ≫ (Functor.curryObjProdComp L L U).hom) I F
  change L.map (derivedProjectionFormulaMate L R adj T U b I F) ≫
      adj.counit.app (U.obj (I, L.obj F)) =
    (b.hom.app (R.obj I, F) ≫ 𝟙 _) ≫
      U.map (Prod.mkHom (adj.counit.app I) (𝟙 (L.obj F))) at h
  simpa only [Category.comp_id] using h

private theorem proEtale_projection_counit
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)
    (a : ProEtaleTensorModel Y R) (b : ProEtaleTensorModel X S)
    (I : DerivedCategory (proEtaleRingModules X S))
    (F : DerivedCategory (proEtaleRingModules Y R)) :
    (proEtaleRingDerivedPullback f R S c).map
        (proEtaleProjectionFormulaMate f R S c a b I F) ≫
      (proEtaleRingDerivedAdjunction f R S c).counit.app
        (b.tensor.obj (I, (proEtaleRingDerivedPullback f R S c).obj F)) =
    (proEtaleCanonicalTensorComparison f R S c a b).hom.app
        ((proEtaleRingDerivedDirectImage f R S c).obj I, F) ≫
      b.tensor.map (Prod.mkHom
        ((proEtaleRingDerivedAdjunction f R S c).counit.app I)
        (𝟙 ((proEtaleRingDerivedPullback f R S c).obj F))) := by
  exact projection_counit _ _ _ _ _ _ I F

attribute [local irreducible] proEtaleProjectionFormulaMate

private theorem localized_counit_composite
    {C : Type uA} [Category.{vA} C] {D : Type uB} [Category.{vB} D]
    {C' : Type u'} [Category.{v'} C'] {D' : Type u} [Category.{v} D']
    (Q : C ⥤ C') (Q' : D ⥤ D') (L : C ⥤ D) (LD : C' ⥤ D')
    (eps : Q ⋙ LD ⟶ L ⋙ Q')
    {P A B : C} {J : D} {S T Z : C'}
    (p : P ⟶ A) (t : A ⟶ B) (e : L.obj B ⟶ J)
    (s : S ⟶ Q.obj P) (h : S ⟶ T) (m : T ⟶ Q.obj A)
    (eta : Q.obj B ⟶ Z) (c : LD.obj Z ⟶ Q'.obj J)
    (hs : h ≫ m = s ≫ Q.map p)
    (hc : LD.map eta ≫ c = eps.app B ≫ Q'.map e) :
    LD.map (h ≫ m ≫ Q.map t ≫ eta) ≫ c =
      LD.map s ≫ eps.app P ≫ Q'.map (L.map p ≫ L.map t ≫ e) := by
  rw [← Category.assoc h, hs]
  simp only [LD.map_comp, Category.assoc]
  rw [hc]
  change LD.map s ≫ (Q ⋙ LD).map p ≫ (Q ⋙ LD).map t ≫ _ = _
  rw [eps.naturality_assoc t, eps.naturality_assoc p]
  simp only [Functor.comp_map, ← Q'.map_comp]

private theorem inverse_normalization
    {C : Type uA} [Category.{vA} C] {D : Type uB} [Category.{vB} D]
    (F : C ⥤ D) {X₀ X₁ : C} {Y₀ Y₁ : D} (a : X₀ ≅ X₁) (b : Y₀ ≅ Y₁)
    (m : F.obj X₁ ⟶ Y₁) (z : F.obj X₀ ⟶ Y₀)
    (h : F.map a.hom ≫ m = z ≫ b.hom) :
    m ≫ b.inv = F.map a.inv ≫ z := by
  apply (cancel_epi (F.map a.hom)).mp
  simp only [← Category.assoc, ← F.map_comp, Iso.hom_inv_id,
    F.map_id, Category.id_comp]
  rw [h, Category.assoc, Iso.hom_inv_id, Category.comp_id]

private theorem assoc_equality
    {C : Type uA} [Category.{vA} C] {A B D E : C}
    (a : A ⟶ B) (b : B ⟶ D) (c : D ⟶ E) {z : A ⟶ E}
    (h : (a ≫ b) ≫ c = z) : a ≫ b ≫ c = z :=
  (Category.assoc a b c).symm.trans h

private theorem transpose_injective
    {C : Type uA} [Category.{vA} C] {D : Type uB} [Category.{vB} D]
    (L : C ⥤ D) (V : D ⥤ C) (adj : L ⊣ V)
    {A : C} {B : D} (f g : A ⟶ V.obj B)
    (h : L.map f ≫ adj.counit.app B = L.map g ≫ adj.counit.app B) : f = g := by
  apply (adj.homEquiv A B).symm.injective
  exact h

private theorem mate_calculation
    {C : Type uA} [Category.{vA} C] {D : Type uB} [Category.{vB} D]
    (L : C ⥤ D) (V : D ⥤ C) (adj : L ⊣ V)
    (T : C × C ⥤ C) (U : D × D ⥤ D)
    {P F M : C} {I G J N H : D}
    (x : T.obj (P, F) ⟶ T.obj (V.obj I, F))
    (pi : T.obj (V.obj I, F) ⟶ V.obj (U.obj (I, L.obj F)))
    (bP : L.obj (T.obj (P, F)) ⟶ U.obj (L.obj P, L.obj F))
    (bI : L.obj (T.obj (V.obj I, F)) ⟶ U.obj (L.obj (V.obj I), L.obj F))
    (epsP : L.obj P ⟶ N) (epsF : L.obj F ⟶ G) (v : N ⟶ I)
    (mP : U.obj (N, G) ⟶ H) (mI : U.obj (I, G) ⟶ J) (z : H ⟶ J)
    (rho : T.obj (P, F) ⟶ M) (epsM : L.obj M ⟶ H)
    (hp : L.map pi ≫ adj.counit.app (U.obj (I, L.obj F)) =
      bI ≫ U.map (Prod.mkHom (adj.counit.app I) (𝟙 (L.obj F))))
    (hb : L.map x ≫ bI ≫
      U.map (Prod.mkHom (adj.counit.app I) epsF) =
        bP ≫ U.map (Prod.mkHom (epsP ≫ v) epsF))
    (hm : U.map (Prod.mkHom v (𝟙 G)) ≫ mI = mP ≫ z)
    (hr : bP ≫ U.map (Prod.mkHom epsP epsF) ≫ mP = L.map rho ≫ epsM) :
    L.map (x ≫ pi ≫ V.map (U.map (Prod.mkHom (𝟙 I) epsF) ≫ mI)) ≫
        adj.counit.app J = L.map rho ≫ epsM ≫ z := by
  simp only [L.map_comp, Category.assoc]
  have hn := adj.counit.naturality (U.map (Prod.mkHom (𝟙 I) epsF) ≫ mI)
  change L.map (V.map (U.map (Prod.mkHom (𝟙 I) epsF) ≫ mI)) ≫
    adj.counit.app J = _ at hn
  rw [hn, reassoc_of% hp]
  simp only [Functor.id_map]
  rw [← U.map_comp_assoc]
  simp only [prod_comp, Category.comp_id, Category.id_comp]
  rw [reassoc_of% hb]
  have ht : U.map (Prod.mkHom (epsP ≫ v) epsF) =
      U.map (Prod.mkHom epsP epsF) ≫ U.map (Prod.mkHom v (𝟙 G)) := by
    simp only [← U.map_comp, prod_comp, Category.comp_id]
  rw [ht]
  simp only [Category.assoc]
  rw [hm, reassoc_of% hr]

private theorem total_naturality
    {A : Type uA} [Category.{vA} A] [Abelian A] [MonoidalCategory A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [MonoidalCategory B]
    [MonoidalPreadditive A] [MonoidalPreadditive B]
    [HasCoproducts.{0} A] [HasCoproducts.{0} B]
    (L : A ⥤ B) [L.Additive]
    (e : ∀ X Y : A, L.obj (X ⊗ Y) ≅ L.obj X ⊗ L.obj Y)
    (he : ∀ {X X' Y Y' : A} (p : X ⟶ X') (q : Y ⟶ Y'),
      L.map (p ⊗ₘ q) ≫ (e X' Y').hom = (e X Y).hom ≫ (L.map p ⊗ₘ L.map q))
    {P P' F : CochainComplex A ℤ} (p : P ⟶ P') :
    let LC := L.mapHomologicalComplex (.up ℤ)
    let UY := ((curriedTensor A).map₂HomologicalComplex
      (.up ℤ) (.up ℤ) (.up ℤ)).flip.obj F
    let UX := ((curriedTensor B).map₂HomologicalComplex
      (.up ℤ) (.up ℤ) (.up ℤ)).flip.obj (LC.obj F)
    UX.map (LC.map p) ≫ tensorPullbackTotal L e he P' F =
      tensorPullbackTotal L e he P F ≫ LC.map (UY.map p) := by
  have hh := SheafOfModules.CanonicalTensorPullbackOfUniverses.tensorPullbackTotal_naturality
    L e he p (𝟙 F)
  rw [(L.mapHomologicalComplex (.up ℤ)).map_id F] at hh
  simpa only [HomologicalComplex.mapBifunctorMap, Functor.map_id, Functor.flip_obj_map,
    Functor.map₂HomologicalComplex_map_app, Category.comp_id] using hh

private theorem total_counit
    {A : Type uA} [Category.{vA} A] [Abelian A] [MonoidalCategory A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [MonoidalCategory B]
    [MonoidalPreadditive A] [MonoidalPreadditive B]
    [HasCoproducts.{0} A] [HasCoproducts.{0} B]
    (L : A ⥤ B) (V : B ⥤ A) [L.Additive] [V.Additive] (am : L ⊣ V)
    (e : ∀ X Y : A, L.obj (X ⊗ Y) ≅ L.obj X ⊗ L.obj Y)
    (he : ∀ {X X' Y Y' : A} (p : X ⟶ X') (q : Y ⟶ Y'),
      L.map (p ⊗ₘ q) ≫ (e X' Y').hom = (e X Y).hom ≫ (L.map p ⊗ₘ L.map q))
    (I : CochainComplex B ℤ) (F : CochainComplex A ℤ) :
    letI := tensorPullbackTotal_isIso L e he V am
      ((V.mapHomologicalComplex (.up ℤ)).obj I) F
    (L.mapHomologicalComplex (.up ℤ)).map (tensorAdjunctionTotal L V am e he I F) ≫
        (am.mapHomologicalComplex (.up ℤ)).counit.app
          (CochainComplex.mapBifunctor I ((L.mapHomologicalComplex (.up ℤ)).obj F)
            (curriedTensor B)) =
      inv (tensorPullbackTotal L e he ((V.mapHomologicalComplex (.up ℤ)).obj I) F) ≫
        HomologicalComplex.mapBifunctorMap
          ((am.mapHomologicalComplex (.up ℤ)).counit.app I)
          (𝟙 ((L.mapHomologicalComplex (.up ℤ)).obj F)) (curriedTensor B) (.up ℤ) := by
  change ((am.mapHomologicalComplex (.up ℤ)).homEquiv _ _).symm
    ((am.mapHomologicalComplex (.up ℤ)).homEquiv _ _ _) = _
  exact Equiv.symm_apply_apply _ _

private theorem proEtale_cochain_counit
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)
    (I : CochainComplex (proEtaleRingModules X S) ℤ) :
    (proEtaleRingDerivedPullback f R S c).map
        ((proEtaleRingModuleDirectImage f R S c).rightDerivedFunctorUnit.app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj I)) ≫
      (proEtaleRingDerivedAdjunction f R S c).counit.app (DerivedCategory.Q.obj I) =
      (proEtaleRingDerivedPullbackFactors f R S c).hom.app
          (((proEtaleRingModuleDirectImage f R S c).mapHomologicalComplex (.up ℤ)).obj I) ≫
        DerivedCategory.Q.map
          (((proEtaleRingModuleAdjunction f R S c).mapHomologicalComplex (.up ℤ)).counit.app I) :=
  cochain_counit _ _ (proEtaleRingModuleAdjunction f R S c) I

attribute [local irreducible] proEtaleRingDerivedPullbackFactors
attribute [local irreducible] proEtaleRingModulePullback proEtaleRingModuleAdjunction
  proEtaleRingDerivedAdjunction

/-- The ordinary signed-total projection mate, with its explicit complex type. -/
def proEtaleProjectionTotal
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)
    (I : CochainComplex (proEtaleRingModules X S) ℤ)
    (F : CochainComplex (proEtaleRingModules Y R) ℤ) :
    CochainComplex.mapBifunctor
      (((proEtaleRingModuleDirectImage f R S c).mapHomologicalComplex (.up ℤ)).obj I)
      F (proEtaleOrdinaryTensor Y R) ⟶
    ((proEtaleRingModuleDirectImage f R S c).mapHomologicalComplex (.up ℤ)).obj
      (CochainComplex.mapBifunctor I
        (((proEtaleRingModulePullback f R S c).mapHomologicalComplex (.up ℤ)).obj F)
        (proEtaleOrdinaryTensor X S)) := by
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.monoidalCategory S
  exact tensorAdjunctionTotal (proEtaleRingModulePullback f R S c)
    (proEtaleRingModuleDirectImage f R S c) (proEtaleRingModuleAdjunction f R S c)
    (proEtaleOrdinaryTensorPullback f R S c)
    (fun {_ _ _ _} v z ↦ by
      simpa only [proEtaleOrdinaryTensor, curriedTensor, tensorHom_def, Category.assoc] using
        proEtaleOrdinaryTensorPullback_naturality f R S c _ _ _ _ v z) I F

attribute [local irreducible] CategoryTheory.tensorAdjunctionTotal proEtaleProjectionTotal

attribute [local instance 2000] Limits.instHasColimitOfHasColimitsOfShape
  Limits.instHasLimitOfHasLimitsOfShape

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
set_option maxHeartbeats 200000 in
-- Nested localization comparisons require extra elaboration steps.
/-- The derived counit mate is the localization of the ordinary total mate on mixed
representatives. Only the coefficient complex is required to be flat and K-flat;
no finite-projective splitting or inverse projection map is involved. -/
theorem proEtaleMixedProjectionMate
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)
    (a : ProEtaleTensorModel Y R) (b : ProEtaleTensorModel X S)
    (I : CochainComplex (proEtaleRingModules X S) ℤ) (_hI : I.IsKInjective)
    (F : CochainComplex (proEtaleRingModules Y R) ℤ)
    (hF : proEtaleFlatRepresentatives Y R F) :
    let L := proEtaleRingModulePullback f R S c
    let V := proEtaleRingModuleDirectImage f R S c
    let G := (L.mapHomologicalComplex (.up ℤ)).obj F
    let J := CochainComplex.mapBifunctor I G (proEtaleOrdinaryTensor X S)
    let hG := (proEtaleCanonicalTensorPullback f R S c a b).1 F hF
    let eta (C : CochainComplex (proEtaleRingModules X S) ℤ) :
        DerivedCategory.Q.obj ((V.mapHomologicalComplex (.up ℤ)).obj C) ⟶
          (proEtaleRingDerivedDirectImage f R S c).obj (DerivedCategory.Q.obj C) :=
      V.rightDerivedFunctorUnitQ C
    a.tensor.map (Prod.mkHom (eta I) (𝟙 (DerivedCategory.Q.{u + 2}.obj F))) ≫
        proEtaleProjectionFormulaMate f R S c a b
          (DerivedCategory.Q.{u + 2}.obj I) (DerivedCategory.Q.{u + 2}.obj F) ≫
        (proEtaleRingDerivedDirectImage f R S c).map
          (b.tensor.map (Prod.mkHom (𝟙 (DerivedCategory.Q.{u + 2}.obj I))
            ((proEtaleRingDerivedPullbackFactors f R S c).hom.app F)) ≫
              (proEtaleMixedTensor S b I G hG).hom) =
      (proEtaleMixedTensor R a
        ((V.mapHomologicalComplex (.up ℤ)).obj I) F hF).hom ≫
        DerivedCategory.Q.{u + 2}.map (proEtaleProjectionTotal f R S c I F) ≫ eta J := by
  classical
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.monoidalCategory S
  let L := proEtaleRingModulePullback f R S c
  let V := proEtaleRingModuleDirectImage f R S c
  let LD := proEtaleRingDerivedPullback f R S c
  let VD := proEtaleRingDerivedDirectImage f R S c
  let adj := proEtaleRingDerivedAdjunction f R S c
  let am := proEtaleRingModuleAdjunction f R S c
  let A := (V.mapHomologicalComplex (.up ℤ)).obj I
  let G := (L.mapHomologicalComplex (.up ℤ)).obj F
  let J := CochainComplex.mapBifunctor I G (proEtaleOrdinaryTensor X S)
  let eta (C : CochainComplex (proEtaleRingModules X S) ℤ) :
      DerivedCategory.Q.obj ((V.mapHomologicalComplex (.up ℤ)).obj C) ⟶
        VD.obj (DerivedCategory.Q.obj C) :=
    V.rightDerivedFunctorUnitQ C
  let hG := (proEtaleCanonicalTensorPullback f R S c a b).1 F hF
  let beta := proEtaleCanonicalTensorComparison f R S c a b
  let eps := (proEtaleRingDerivedPullbackFactors f R S c).hom
  let epsc := (am.mapHomologicalComplex (.up ℤ)).counit.app I
  let total := proEtaleProjectionTotal f R S c I F
  change a.tensor.map (Prod.mkHom (eta I) (𝟙 (DerivedCategory.Q.obj F))) ≫
      proEtaleProjectionFormulaMate f R S c a b
        (DerivedCategory.Q.obj I) (DerivedCategory.Q.obj F) ≫
      VD.map (b.tensor.map (Prod.mkHom (𝟙 (DerivedCategory.Q.obj I)) (eps.app F)) ≫
        (proEtaleMixedTensor S b I G hG).hom) =
    (proEtaleMixedTensor R a A F hF).hom ≫ DerivedCategory.Q.map total ≫ eta J
  have hc (I : CochainComplex (proEtaleRingModules X S) ℤ) :
      LD.map (eta I) ≫ adj.counit.app (DerivedCategory.Q.{u + 2}.obj I) =
      eps.app ((V.mapHomologicalComplex (.up ℤ)).obj I) ≫
        DerivedCategory.Q.{u + 2}.map
          ((am.mapHomologicalComplex (.up ℤ)).counit.app I) := by
    have heta : eta I =
        V.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ (.up ℤ)).obj I) := by
      simp only [eta, Functor.rightDerivedFunctorUnitQ, DerivedCategory.quotientCompQhIso,
        HomologicalComplexUpToQuasiIso.quotientCompQhIso, Quotient.lift.isLift,
        NatIso.ofComponents_hom_app, NatIso.ofComponents_inv_app, Iso.refl_hom, Iso.refl_inv]
      erw [Category.id_comp, CategoryTheory.Functor.map_id, Category.comp_id]
    rw [heta]
    exact proEtale_cochain_counit f R S c I
  obtain ⟨D, q, hres⟩ := flat_resolution_functor Y R
  let P := D.obj A
  let p := q.app A
  have hP : proEtaleFlatRepresentatives Y R P := (hres A).1
  have hq : QuasiIso p := (hres A).2
  have : QuasiIso p := hq
  have : IsIso (Prod.mkHom (DerivedCategory.Q.{u + 2}.map p)
      (𝟙 (DerivedCategory.Q.{u + 2}.obj F))) :=
    (Iso.prod (asIso (DerivedCategory.Q.{u + 2}.map p)) (Iso.refl _)).isIso_hom
  apply (cancel_epi (a.tensor.map
    (Prod.mkHom (DerivedCategory.Q.{u + 2}.map p) (𝟙 (DerivedCategory.Q.{u + 2}.obj F))))).mp
  have hs := mixed_normalization Y R a A F P hF hP p hq
  rw [representativeInv_eq] at hs
  have hLP := (proEtaleCanonicalTensorPullback f R S c a b).1 P hP
  have ht := tensor_comparison_normalization f R S c a b P F hP hF hLP hG
  let LP := (L.mapHomologicalComplex (.up ℤ)).obj P
  let v := (L.mapHomologicalComplex (.up ℤ)).map p ≫ epsc
  have hm := mixed_naturality X S b LP I G hG v
  have hmP := mixed_normalization X S b LP G LP hG hLP (𝟙 LP) (by infer_instance)
  have hid : HomologicalComplex.mapBifunctorMap (𝟙 LP) (𝟙 G)
      (proEtaleOrdinaryTensor X S) (.up ℤ) = 𝟙 _ := by
    simp [HomologicalComplex.mapBifunctorMap]
  simp only [DerivedCategory.Q.{u + 2}.map_id, ← prod_id, hid] at hmP
  change b.tensor.map (𝟙 (DerivedCategory.Q.obj LP, DerivedCategory.Q.obj G)) ≫ _ = _ at hmP
  rw [b.tensor.map_id, Category.id_comp] at hmP
  erw [Category.comp_id] at hmP
  rw [representativeInv_eq] at hmP
  have hcv : LD.map (DerivedCategory.Q.map p ≫ eta I) ≫
      adj.counit.app (DerivedCategory.Q.obj I) =
      eps.app P ≫ DerivedCategory.Q.map v := by
    rw [Functor.map_comp, Category.assoc, hc I, ← Category.assoc]
    have hn := eps.naturality p
    change LD.map (DerivedCategory.Q.map p) ≫ eps.app A =
      eps.app P ≫ DerivedCategory.Q.map
        ((L.mapHomologicalComplex (.up ℤ)).map p) at hn
    rw [hn, Category.assoc, ← Functor.map_comp]
  have hb : LD.map (a.tensor.map
        (Prod.mkHom (DerivedCategory.Q.map p ≫ eta I) (𝟙 (DerivedCategory.Q.obj F)))) ≫
      beta.hom.app (VD.obj (DerivedCategory.Q.obj I), DerivedCategory.Q.obj F) ≫
      b.tensor.map (Prod.mkHom (adj.counit.app (DerivedCategory.Q.obj I)) (eps.app F)) =
      beta.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj F) ≫
        b.tensor.map (Prod.mkHom (eps.app P ≫ DerivedCategory.Q.map v) (eps.app F)) := by
    have hn := beta.hom.naturality
      (Prod.mkHom (DerivedCategory.Q.map p ≫ eta I) (𝟙 (DerivedCategory.Q.obj F)))
    change LD.map (a.tensor.map
        (Prod.mkHom (DerivedCategory.Q.map p ≫ eta I)
          (𝟙 (DerivedCategory.Q.obj F)))) ≫
        beta.hom.app (VD.obj (DerivedCategory.Q.obj I), DerivedCategory.Q.obj F) =
      beta.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj F) ≫ b.tensor.map
        (Prod.mkHom (LD.map (DerivedCategory.Q.map p ≫ eta I))
          (LD.map (𝟙 (DerivedCategory.Q.obj F)))) at hn
    rw [← Category.assoc, hn, Category.assoc, ← b.tensor.map_comp]
    simp only [prod_comp, LD.map_id, hcv]
    erw [Category.id_comp]
  have hpi : LD.map (proEtaleProjectionFormulaMate f R S c a b
        (DerivedCategory.Q.obj I) (DerivedCategory.Q.obj F)) ≫
      adj.counit.app (b.tensor.obj
        (DerivedCategory.Q.obj I, LD.obj (DerivedCategory.Q.obj F))) =
      beta.hom.app (VD.obj (DerivedCategory.Q.obj I), DerivedCategory.Q.obj F) ≫
        b.tensor.map (Prod.mkHom (adj.counit.app (DerivedCategory.Q.obj I))
          (𝟙 (LD.obj (DerivedCategory.Q.obj F)))) := by
    exact proEtale_projection_counit f R S c a b
      (DerivedCategory.Q.obj I) (DerivedCategory.Q.obj F)
  have hrep : beta.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj F) ≫
      b.tensor.map (Prod.mkHom (eps.app P) (eps.app F)) ≫
      representativeInv X S b LP G hLP hG =
      LD.map (representativeInv Y R a P F hP hF) ≫
        eps.app (CochainComplex.mapBifunctor P F (proEtaleOrdinaryTensor Y R)) ≫
        (DerivedCategory.Q.mapIso (proEtaleTensorPullbackTotalIso f R S c P F)).inv := by
    have hh := inverse_normalization LD
      (a.representative.app (⟨P, hP⟩, ⟨F, hF⟩))
      (b.representative.app (⟨LP, hLP⟩, ⟨G, hG⟩))
      (beta.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj F) ≫
        b.tensor.map (Prod.mkHom (eps.app P) (eps.app F)))
      (eps.app (CochainComplex.mapBifunctor P F (proEtaleOrdinaryTensor Y R)) ≫
        (DerivedCategory.Q.mapIso (proEtaleTensorPullbackTotalIso f R S c P F)).inv)
      (by
        set_option backward.isDefEq.respectTransparency false in
        set_option backward.isDefEq.respectTransparency.types false in
        exact (by
          simpa only [beta, Category.assoc, Iso.app_hom] using ht))
    simp only [Iso.app_inv, representativeInv_eq] at hh
    exact assoc_equality _ _ _ hh
  let muP := proEtaleTensorPullbackTotalIso f R S c P F
  let muA := proEtaleTensorPullbackTotalIso f R S c A F
  let LC := L.mapHomologicalComplex (.up ℤ)
  let UY := ((proEtaleOrdinaryTensor Y R).map₂HomologicalComplex
    (.up ℤ) (.up ℤ) (.up ℤ)).flip.obj F
  let UX := ((proEtaleOrdinaryTensor X S).map₂HomologicalComplex
    (.up ℤ) (.up ℤ) (.up ℤ)).flip.obj G
  have htc : LC.map total ≫ (am.mapHomologicalComplex (.up ℤ)).counit.app J =
      muA.inv ≫ UX.map epsc := by
    unfold total proEtaleProjectionTotal
    exact total_counit L V am (proEtaleOrdinaryTensorPullback f R S c)
      (fun {_ _ _ _} p q ↦ by
        simpa only [proEtaleOrdinaryTensor, curriedTensor, tensorHom_def, Category.assoc] using
          proEtaleOrdinaryTensorPullback_naturality f R S c _ _ _ _ p q)
      I F
  have hmu : UX.map (LC.map p) ≫ muA.hom = muP.hom ≫ LC.map (UY.map p) := by
    exact total_naturality L (proEtaleOrdinaryTensorPullback f R S c)
      (fun {_ _ _ _} v z ↦ by
        simpa only [proEtaleOrdinaryTensor, curriedTensor, tensorHom_def, Category.assoc] using
          proEtaleOrdinaryTensorPullback_naturality f R S c _ _ _ _ v z) (F := F) p
  have hchain : muP.inv ≫ UX.map v =
      LC.map (UY.map p) ≫ LC.map total ≫
        (am.mapHomologicalComplex (.up ℤ)).counit.app J := by
    set_option backward.isDefEq.respectTransparency false in
    set_option backward.isDefEq.respectTransparency.types false in
    exact (by
      have hh : muP.inv ≫ UX.map (LC.map p) = LC.map (UY.map p) ≫ muA.inv := by
        apply (cancel_mono muA.hom).mp
        simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
        rw [hmu, Iso.inv_hom_id_assoc]
      dsimp only [v]
      rw [UX.map_comp, ← Category.assoc, hh, Category.assoc, ← htc]
    )
  let B := b.tensor.map (Prod.mkHom (𝟙 (DerivedCategory.Q.obj I)) (eps.app F)) ≫
    (proEtaleMixedTensor S b I G hG).hom
  have hleft : LD.map
      (a.tensor.map (Prod.mkHom (DerivedCategory.Q.map p ≫ eta I)
        (𝟙 (DerivedCategory.Q.obj F))) ≫
        proEtaleProjectionFormulaMate f R S c a b
          (DerivedCategory.Q.obj I) (DerivedCategory.Q.obj F) ≫ VD.map B) ≫
        adj.counit.app (DerivedCategory.Q.obj J) =
      LD.map (representativeInv Y R a P F hP hF) ≫
        eps.app (CochainComplex.mapBifunctor P F (proEtaleOrdinaryTensor Y R)) ≫
        DerivedCategory.Q.map (muP.inv ≫ UX.map v) := by
    have hh := mate_calculation LD VD adj a.tensor b.tensor
      (a.tensor.map (Prod.mkHom (DerivedCategory.Q.map p ≫ eta I)
        (𝟙 (DerivedCategory.Q.obj F))))
      (proEtaleProjectionFormulaMate f R S c a b
        (DerivedCategory.Q.obj I) (DerivedCategory.Q.obj F))
      (beta.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj F))
      (beta.hom.app (VD.obj (DerivedCategory.Q.obj I), DerivedCategory.Q.obj F))
      (eps.app P) (eps.app F) (DerivedCategory.Q.map v)
      (representativeInv X S b LP G hLP hG)
      (proEtaleMixedTensor S b I G hG).hom (DerivedCategory.Q.map (UX.map v))
      (representativeInv Y R a P F hP hF)
      (eps.app (CochainComplex.mapBifunctor P F (proEtaleOrdinaryTensor Y R)) ≫
        (DerivedCategory.Q.mapIso muP).inv) hpi hb
      (by
        set_option backward.isDefEq.respectTransparency true in
        set_option backward.isDefEq.respectTransparency.types true in
        exact hm.trans (congrArg (fun z ↦ z ≫ DerivedCategory.Q.map
          (HomologicalComplex.mapBifunctorMap v (𝟙 G)
            (proEtaleOrdinaryTensor X S) (.up ℤ))) hmP))
      (by simpa only [Category.assoc] using hrep)
    set_option backward.isDefEq.respectTransparency false in
    set_option backward.isDefEq.respectTransparency.types false in
    exact (by
      simpa only [B, J, Functor.mapIso_inv, Category.assoc,
        ← (DerivedCategory.Q (C := proEtaleRingModules X S)).map_comp,
        quotient_obj] using hh)
  have hright : LD.map
      (a.tensor.map (Prod.mkHom (DerivedCategory.Q.map p)
        (𝟙 (DerivedCategory.Q.obj F))) ≫
        (proEtaleMixedTensor R a A F hF).hom ≫
          DerivedCategory.Q.map total ≫ eta J) ≫
        adj.counit.app (DerivedCategory.Q.obj J) =
      LD.map (representativeInv Y R a P F hP hF) ≫
        eps.app (CochainComplex.mapBifunctor P F (proEtaleOrdinaryTensor Y R)) ≫
        DerivedCategory.Q.map (LC.map (UY.map p) ≫ LC.map total ≫
          (am.mapHomologicalComplex (.up ℤ)).counit.app J) := by
    set_option backward.isDefEq.respectTransparency false in
    set_option backward.isDefEq.respectTransparency.types false in
    exact (by
      apply localized_counit_composite
        (DerivedCategory.Q (C := proEtaleRingModules Y R))
        (DerivedCategory.Q (C := proEtaleRingModules X S)) LC LD eps
        (UY.map p) total ((am.mapHomologicalComplex (.up ℤ)).counit.app J)
        (representativeInv Y R a P F hP hF)
        (a.tensor.map (Prod.mkHom (DerivedCategory.Q.map p)
          (𝟙 (DerivedCategory.Q.obj F))))
        (proEtaleMixedTensor R a A F hF).hom (eta J) (adj.counit.app _)
      · exact hs
      · simpa only [J, V, G, proEtaleOrdinaryTensor, Functor.id_obj, quotient_obj,
          Functor.comp_obj] using hc J
    )
  change a.tensor.map (Prod.mkHom (DerivedCategory.Q.map p)
      (𝟙 (DerivedCategory.Q.obj F))) ≫
    a.tensor.map (Prod.mkHom (eta I) (𝟙 (DerivedCategory.Q.obj F))) ≫
    proEtaleProjectionFormulaMate f R S c a b
      (DerivedCategory.Q.obj I) (DerivedCategory.Q.obj F) ≫ VD.map B = _
  have hx : a.tensor.map (Prod.mkHom (DerivedCategory.Q.map p)
      (𝟙 (DerivedCategory.Q.obj F))) ≫
      a.tensor.map (Prod.mkHom (eta I) (𝟙 (DerivedCategory.Q.obj F))) =
    a.tensor.map (Prod.mkHom (DerivedCategory.Q.map p ≫ eta I)
      (𝟙 (DerivedCategory.Q.obj F))) := by
    rw [← a.tensor.map_comp]
    rfl
  rw [reassoc_of% hx]
  apply transpose_injective LD VD adj
  exact hleft.trans ((congrArg (fun z ↦
    LD.map (representativeInv Y R a P F hP hF) ≫
      eps.app (CochainComplex.mapBifunctor P F (proEtaleOrdinaryTensor Y R)) ≫
        DerivedCategory.Q.map z) hchain).trans hright.symm)

end AlgebraicGeometry.Scheme
