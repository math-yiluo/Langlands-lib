/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.OrderedExchange.ProEtaleConstantReductionModels
public import WeilConjectures.AlgebraicGeometry.StrictTower.StrictConstantTowerOperationsSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Canonical.ProEtaleCanonicalTensorPullback
import all WeilConjectures.AlgebraicGeometry.OrderedExchange.ProEtaleConstantReductionModels
import all WeilConjectures.AlgebraicGeometry.DerivedScalarMate.DerivedScalarMateData
import all WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
import WeilConjectures.Algebra.Homology.CochainTensorModelRigidity
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.Tactic.TransportExact
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Localization.Construction
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.CategoryTheory.Whiskering
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Localization.Prod
import Mathlib.Algebra.Homology.BifunctorFlip
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorHomotopy
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.CategoryTheory.Localization.CalculusOfFractions
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.AlgebraicGeometry.Completed.Constant.CompletedConstantRankOneComparison
import WeilConjectures.AlgebraicGeometry.CompletedConstantProjection.CompletedConstantResidueData
import all WeilConjectures.AlgebraicGeometry.DerivedScalarMate.ScalarMateOrdinaryModuleRoute
import WeilConjectures.Algebra.Homology.BifunctorSingleComparison
import WeilConjectures.AlgebraicGeometry.ProEtale.Tensor.ProEtaleTensorPullbackDescentData

/-! # Tensor interpretation of one evaluated constant reduction

## References

* Stacks Tags 06YY, 07A4, 099M and 0B56
* Stacks Tags 06YY (derived localization), 07A4 (derived tensor), 099M (adic reduction)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.OrderedExchange
variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)
variable {U V : Scheme.{t}} (f : U ⟶ V)

attribute [local irreducible] SheafOfModules.monoidalCategory
  Functor.mapDerivedCategory Functor.leftAdjoint presheafToSheaf
attribute [local implicit_reducible] Functor.map₂HomologicalComplex

private theorem exactSquareFactors
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (L : A ⥤ B) (L' : C ⥤ D) (G : A ⥤ C) (H : B ⥤ D)
    [L.Additive] [L'.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits L'] [PreservesFiniteColimits L']
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (s : G ⋙ L' ≅ L ⋙ H) (K : CochainComplex A ℤ) :
    (Functor.mapDerivedCategoryCompIso G L' ≪≫
        Functor.mapDerivedCategoryNatIso s ≪≫ (Functor.mapDerivedCategoryCompIso L H).symm).hom.app
          (DerivedCategory.Q.obj K) ≫
        H.mapDerivedCategory.map (L.mapDerivedCategoryFactors.hom.app K) ≫
        H.mapDerivedCategoryFactors.hom.app ((L.mapHomologicalComplex (.up ℤ)).obj K) =
      L'.mapDerivedCategory.map (G.mapDerivedCategoryFactors.hom.app K) ≫
        L'.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex s.hom (.up ℤ)).app K) := by
  have h₁ := Functor.mapDerivedCategoryCompIso_fac L H K
  have h₂ := Functor.mapDerivedCategoryCompIso_fac G L' K
  have h₃ := Functor.mapDerivedCategoryNatIso_fac s K
  have hL : (Functor.mapHomologicalComplexCompIso (Iso.refl (L ⋙ H)) (.up ℤ)).hom.app K =
      𝟙 _ := rfl
  have hG : (Functor.mapHomologicalComplexCompIso (Iso.refl (G ⋙ L')) (.up ℤ)).hom.app K =
      𝟙 _ := rfl
  erw [hL, DerivedCategory.Q.map_id, Category.comp_id] at h₁
  erw [hG, DerivedCategory.Q.map_id, Category.comp_id] at h₂
  apply (cancel_epi
    ((Functor.mapDerivedCategoryCompIso G L').inv.app (DerivedCategory.Q.obj K))).1
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc,
    Iso.inv_hom_id_app_assoc]
  erw [h₁, h₃, ← reassoc_of% h₂]

private theorem tensorTotalExists {W : Scheme.{t}}
    (R : Sheaf (ProEt.topology W) CommRingCat.{t + 1})
    (P Q : CochainComplex (proEtaleRingModules W R) ℤ) :
    HomologicalComplex.HasMapBifunctor P Q (proEtaleOrdinaryTensor W R) (.up ℤ) :=
  fun _ ↦ @HasColimitsOfShape.has_colimit _ _ _ _
    (@HasColimitsOfSize.has_colimits_of_shape _ _
      (inferInstance : HasColimitsOfSize.{0, 0} (proEtaleRingModules W R)) _ _) _

attribute [local instance] tensorTotalExists
attribute [local irreducible] proEtaleRingModulePullback
  proEtaleRingRestrictionPullbackInv
  DerivedScalarMate.ordinaryTensorIso DerivedScalarMate.ordinaryComplexIso
  HomologicalComplex₂.total CategoryTheory.Functor.mapBifunctorHomologicalComplex
  CochainComplex.mapBifunctorSingle₂Iso
set_option backward.defeqAttrib.useBackward true

private def tensorPullbackNat (R : Sheaf (ProEt.topology V) CommRingCat.{t + 1})
    (S : Sheaf (ProEt.topology U) CommRingCat.{t + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{t + 1}).obj R ≅ S) :
    (CategoryTheory.Functor.postcompose₂.obj
      (proEtaleRingModulePullback f R S c)).obj
        (proEtaleOrdinaryTensor V R) ⟶
    (((CategoryTheory.Functor.whiskeringLeft₂ (proEtaleRingModules U (S))).obj
      (proEtaleRingModulePullback f R S c)).obj
      (proEtaleRingModulePullback f R S c)).obj
        (proEtaleOrdinaryTensor U (S)) where
  app M :=
    { app := fun N ↦ (proEtaleOrdinaryTensorPullback f R S c M N).hom
      naturality := by
        intro N N' z
        dsimp
        simpa only [CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp,
          proEtaleOrdinaryTensor, MonoidalCategory.curriedTensor_obj_map,
          MonoidalCategory.curriedTensor_map_app] using
          proEtaleOrdinaryTensorPullback_naturality f R S c
            M M N N' (𝟙 M) z }
  naturality M M' v := by
    apply NatTrans.ext
    funext N
    dsimp
    have h := proEtaleOrdinaryTensorPullback_naturality
      f R S c M M' N N v (𝟙 N)
    simp only [CategoryTheory.Functor.map_id, Category.comp_id] at h
    exact h

private theorem tensorPullbackColimits (R : Sheaf (ProEt.topology V) CommRingCat.{t + 1})
    (S : Sheaf (ProEt.topology U) CommRingCat.{t + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{t + 1}).obj R ≅ S) :
    ∀ j : ℤ, PreservesColimitsOfShape
      (Discrete ((ComplexShape.up ℤ).π (.up ℤ) (.up ℤ) ⁻¹' {j}))
      (proEtaleRingModulePullback f R S c) := fun _ ↦
  (proEtaleRingModuleAdjunction f R S c
    ).leftAdjoint_preservesColimits.preservesColimitsOfShape

attribute [local instance] tensorPullbackColimits

private theorem tensorPullbackNat_total (R : Sheaf (ProEt.topology V) CommRingCat.{t + 1})
    (S : Sheaf (ProEt.topology U) CommRingCat.{t + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{t + 1}).obj R ≅ S)
    (P Q : CochainComplex (proEtaleRingModules V R) ℤ) :
    (proEtaleTensorPullbackTotalIso f R S c P Q).inv =
      HomologicalComplex.mapBifunctorComparison (tensorPullbackNat f R S c) (.up ℤ) P Q := by
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.monoidalCategory (S)
  apply (cancel_epi
    (proEtaleTensorPullbackTotalIso f R S c P Q).hom).mp
  rw [Iso.hom_inv_id]
  apply HomologicalComplex.hom_ext
  intro n
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j hij
  simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f, Category.comp_id]
  change _ = _ ≫
    (proEtaleTensorPullbackTotal f R S c P Q).f n ≫
      HomologicalComplex.mapBifunctorComparisonX (tensorPullbackNat f R S c)
        (.up ℤ) P Q n
  simp only [proEtaleTensorPullbackTotal, tensorPullbackTotal,
    tensorPullbackTotalComponent, HomologicalComplex.ι_mapBifunctorDesc_assoc]
  erw [Category.assoc, HomologicalComplex.map_ιMapBifunctor_mapBifunctorComparisonX]
  change _ = (proEtaleOrdinaryTensorPullback f R S c
    (P.X i) (Q.X j)).inv ≫
    (proEtaleOrdinaryTensorPullback f R S c
      (P.X i) (Q.X j)).hom ≫ _
  rw [Iso.inv_hom_id_assoc]

private def tensorOneCoefficient
    (R : Sheaf (ProEt.topology V) CommRingCat.{t + 1})
    (S : Sheaf (ProEt.topology U) CommRingCat.{t + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{t + 1}).obj R ≅ S)
    (N : proEtaleRingModules V R) (N' : proEtaleRingModules U S)
    (k : (proEtaleRingModulePullback f R S c).obj N ≅ N') :=
  ((HomologicalComplex.singleMapHomologicalComplex (proEtaleRingModulePullback f R S c)
    (.up ℤ) 0).app N) ≪≫ (CochainComplex.singleFunctor _ (0 : ℤ)).mapIso k

private def tensorOnePullback
    (R : Sheaf (ProEt.topology V) CommRingCat.{t + 1})
    (S : Sheaf (ProEt.topology U) CommRingCat.{t + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{t + 1}).obj R ≅ S)
    (N : proEtaleRingModules V R) (N' : proEtaleRingModules U S)
    (k : (proEtaleRingModulePullback f R S c).obj N ≅ N')
    (P : CochainComplex (proEtaleRingModules V R) ℤ) :=
  (proEtaleTensorPullbackTotalIso f R S c P
    ((CochainComplex.singleFunctor _ (0 : ℤ)).obj N)).inv ≫
    HomologicalComplex.mapBifunctorMap (𝟙 _)
      (tensorOneCoefficient f R S c N N' k).hom (proEtaleOrdinaryTensor U S) (.up ℤ)

private theorem cancel_with_inverse {C : Type*} [Category C]
    {X Y Z : C} {a b : X ⟶ Y} (i : Y ⟶ Z) (j : Z ⟶ Y)
    (hij : i ≫ j = 𝟙 Y) (h : a ≫ i = b ≫ i) : a = b := by
  simpa only [Category.assoc, hij, Category.comp_id] using congrArg (· ≫ j) h

private theorem tensorOnePullback_single_f
    (R : Sheaf (ProEt.topology V) CommRingCat.{t + 1})
    (S : Sheaf (ProEt.topology U) CommRingCat.{t + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{t + 1}).obj R ≅ S)
    (N : proEtaleRingModules V R) (N' : proEtaleRingModules U S)
    (k : (proEtaleRingModulePullback f R S c).obj N ≅ N')
    (P : CochainComplex (proEtaleRingModules V R) ℤ) (n : ℤ) :
    let FA := proEtaleRingModulePullback f R S c
    let FAc := FA.mapHomologicalComplex (.up ℤ)
    (FAc.map (CochainComplex.mapBifunctorSingle₂Iso
      (proEtaleOrdinaryTensor V R) (N) P).inv ≫
      tensorOnePullback f R S c N N' k P ≫
      (CochainComplex.mapBifunctorSingle₂Iso
        (proEtaleOrdinaryTensor U (S)) (N')
        (FAc.obj P)).hom).f n =
    (proEtaleOrdinaryTensorPullback f R S c
      (P.X n) (N)).hom ≫
      ((proEtaleOrdinaryTensor U (S)).obj (FA.obj (P.X n))).map
        (k).hom := by
  let : ∀ K L : CochainComplex (proEtaleRingModules V R) ℤ,
      HomologicalComplex.HasMapBifunctor K L (proEtaleOrdinaryTensor V R) (.up ℤ) :=
    tensorTotalExists R
  let : ∀ K L : CochainComplex (proEtaleRingModules U (S)) ℤ,
      HomologicalComplex.HasMapBifunctor K L
        (proEtaleOrdinaryTensor U (S)) (.up ℤ) :=
    tensorTotalExists (S)
  dsimp only
  let FA := proEtaleRingModulePullback f R S c
  let FAc := FA.mapHomologicalComplex (.up ℤ)
  let TZ := proEtaleOrdinaryTensor U (S)
  let sx := CochainComplex.mapBifunctorSingle₂Iso TZ (N') (FAc.obj P)
  let : ∀ j : ℤ, PreservesColimitsOfShape
      (Discrete ((ComplexShape.up ℤ).π (.up ℤ) (.up ℤ) ⁻¹' {j})) FA :=
    tensorPullbackColimits f R S c
  have hc := CochainComplex.mapBifunctorComparisonX_single₂
    (tensorPullbackNat f R S c) P (N) n
  have ht := congrArg (fun z ↦ z.f n)
    (tensorPullbackNat_total f R S c P
      ((HomologicalComplex.single _ (.up ℤ) 0).obj (N)))
  change (proEtaleTensorPullbackTotalIso f R S c P
      ((HomologicalComplex.single _ (.up ℤ) 0).obj (N))).inv.f n =
    HomologicalComplex.mapBifunctorComparisonX (tensorPullbackNat f R S c)
      (.up ℤ) P ((HomologicalComplex.single _ (.up ℤ) 0).obj (N)) n at ht
  rw [← ht] at hc
  have hk := congrArg (fun z ↦ z.f n)
    (CochainComplex.mapBifunctorSingle₂Iso_inv_naturality₂ TZ k.hom (FAc.obj P))
  simp only [HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f] at hk
  have hsx := congrArg (fun z ↦ z.f n) sx.hom_inv_id
  simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f] at hsx
  unfold tensorOnePullback tensorOneCoefficient
  simp only [Iso.trans_hom, Iso.app_hom, CategoryTheory.Functor.mapIso_hom]
  have hcomp : HomologicalComplex.mapBifunctorMap (𝟙 (FAc.obj P))
      (((HomologicalComplex.singleMapHomologicalComplex FA (.up ℤ) 0).app
        (N)).hom ≫
        (CochainComplex.singleFunctor (proEtaleRingModules U (S)) (0 : ℤ)).map
          k.hom) TZ (.up ℤ) =
    HomologicalComplex.mapBifunctorMap (𝟙 (FAc.obj P))
      ((HomologicalComplex.singleMapHomologicalComplex FA (.up ℤ) 0).app
        (N)).hom TZ (.up ℤ) ≫
      HomologicalComplex.mapBifunctorMap (𝟙 (FAc.obj P))
        ((CochainComplex.singleFunctor (proEtaleRingModules U (S))
          (0 : ℤ)).map k.hom) TZ (.up ℤ) := by
    exact (TZ.map₂HomologicalComplex (.up ℤ) (.up ℤ) (.up ℤ)).obj (FAc.obj P) |>.map_comp _ _
  erw [hcomp]
  simp only [HomologicalComplex.comp_f, CategoryTheory.Functor.mapHomologicalComplex_map_f,
    Category.assoc]
  have hisx := congrArg (fun z ↦ z.f n) sx.inv_hom_id
  simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f] at hisx
  apply cancel_with_inverse (sx.inv.f n) (sx.hom.f n) hisx
  simp only [Category.assoc]
  erw [hsx, Category.comp_id]
  erw [reassoc_of% hc, ← hk]
  rfl

attribute [local implicit_reducible] proEtaleRingExtension level reductionRestrict
  proEtaleRingModuleDirectImage SheafOfModules.pushforward PresheafOfModules.pushforward
  PresheafOfModules.pushforward₀ PresheafOfModules.pushforward₀Obj
  PresheafOfModules.restrictScalars PresheafOfModules.restrictScalarsObj ModuleCat.restrictScalars
  ModuleCat.RestrictScalars.obj'

private theorem level_additive (T : Scheme.{t}) (n : ℕ) : (level d T n).Additive := by
  dsimp only [level]
  infer_instance

attribute [local instance] level_additive

private theorem tensorModel_exists (T : Scheme.{t})
    (R : Sheaf (ProEt.topology T) CommRingCat.{t + 1}) :
    Nonempty (ProEtaleTensorModel T R) := by
  let i : (proEtaleFlatRepresentatives T R).FullSubcategory ⥤
      (SheafOfModules.cochainTensorFlatRepresentatives (ProEt.topology T) R).FullSubcategory :=
    ObjectProperty.ιOfLE (fun P h ↦
      ⟨(CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).2 h.1, h.2⟩)
  obtain ⟨r, _⟩ := SheafOfModules.cochain_tensor_model_rigidity.{t + 1, t, t + 1, t + 2, 0, 0}
    (ProEt.topology T) R
  exact ⟨⟨SheafOfModules.siteDerivedTensorIndependentCoefficients (ProEt.topology T) R,
    Functor.isoWhiskerLeft (i.prod i) r⟩⟩

private theorem quotient_formula (T : Scheme.{t}) (n : ℕ) :
    quotient d T n =
      (constantSheaf (ProEt.topology T) CommRingCat.{t + 1}).map
        (CommRingCat.ofHom (Ideal.Quotient.mk (d.ideal ^ (n + 1)))) ≫
          (pbcLevelConstantComparison T d n).hom := by
  dsimp only [quotient, exchangeScalar, AdicCoefficientDatum.projection,
    completedReductionProjection, pbcCompletedComparison]
  rw [Category.assoc]
  erw [HasLimit.isoOfNatIso_hom_π]
  rw [← Category.assoc]
  erw [(adicDatumScalar_exists T
    { toCompleteCoefficientDatum := d.toCompleteCoefficientDatum,
      quotientFinite := d.quotientFinite }).exists.choose_spec n]
  rfl

private def unitRestrictionMap (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (e : R ≅ S) :
    SheafOfModules.unit ((adicLisseForget T).obj S) ⟶
      (reductionRestrict T e.inv).obj (SheafOfModules.unit ((adicLisseForget T).obj R)) where
  val :=
    { app := fun W ↦ ModuleCat.ofHom
        (Y := ((reductionRestrict T e.inv).obj
          (SheafOfModules.unit ((adicLisseForget T).obj R))).val.obj W)
        { toFun := e.inv.hom.app W
          map_add' := map_add (e.inv.hom.app W).hom
          map_smul' := map_mul (e.inv.hom.app W).hom }
      naturality := by
        intro W W' v
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro s
        exact ConcreteCategory.congr_hom (e.inv.hom.naturality v) s }

private theorem unitRestrictionMap_isIso (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (e : R ≅ S) :
    IsIso (unitRestrictionMap T e) := by
  let H := SheafOfModules.forget ((adicLisseForget T).obj S) ⋙
    PresheafOfModules.toPresheaf ((adicLisseForget T).obj S).obj
  have (W : T.ProEtᵒᵖ) : IsIso ((H.map (unitRestrictionMap T e)).app W) := by
    apply (ConcreteCategory.isIso_iff_bijective _).2
    change Function.Bijective (fun s : S.obj.obj W ↦ e.inv.hom.app W s)
    exact (ConcreteCategory.isIso_iff_bijective (e.inv.hom.app W)).1 inferInstance
  have : IsIso (H.map (unitRestrictionMap T e)) := NatIso.isIso_of_isIso_app _
  exact isIso_of_reflects_iso (unitRestrictionMap T e) H

private def quotientModuleIso (T : Scheme.{t}) (n : ℕ) :
    (adicLisseConstantModules T A).obj (ModuleCat.of A (A ⧸ d.ideal ^ (n + 1))) ≅
      DerivedScalarMate.coefficient (quotient d T n) := by
  let B := A ⧸ d.ideal ^ (n + 1)
  let r := Ideal.Quotient.mk (d.ideal ^ (n + 1))
  let e := pbcLevelConstantComparison T d n
  let φ := quotient d T n
  let q : (ModuleCat.of A B) →ₛₗ[r] (ModuleCat.of B B) :=
    { toFun := id
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  have hp : φ ≫ e.inv =
      (constantSheaf (ProEt.topology T) CommRingCat.{t + 1}).map (CommRingCat.ofHom r) := by
    dsimp only [φ]
    rw [quotient_formula]
    simp only [e, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rfl
  let a := CompletedConstantProjection.constantMap T r φ e.inv hp
    (ModuleCat.of A B) (ModuleCat.of B B) q
  have : IsIso a := CompletedConstantProjection.constantMap_isIso T r φ e.inv hp
    (ModuleCat.of A B) (ModuleCat.of B B) q Function.bijective_id
  have : IsIso (CompletedConstantRankOne.constantUnit T B) :=
    CompletedConstantRankOne.constantUnit_isIso T B
  have : IsIso (unitRestrictionMap T e) := unitRestrictionMap_isIso T e
  exact asIso a ≪≫ (reductionRestrict T φ).mapIso
    ((reductionRestrict T e.inv).mapIso (asIso (CompletedConstantRankOne.constantUnit T B)) ≪≫
      (asIso (unitRestrictionMap T e)).symm)

private abbrev eval (T : Scheme.{t}) (n : ℕ) :=
  (CategoryTheory.evaluation ℕᵒᵖ
    (reductionModules T (exchangeConstantRing T A))).obj (op n)

private def evalCounit (T : Scheme.{t}) (n : ℕ) :
    DerivedCategory.Q ⋙ reduction d T ⋙ (eval (A := A) T n).mapDerivedCategory ⟶
      (level d T n).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q where
  app P := (eval (A := A) T n).mapDerivedCategory.map (reductionComplexCounit d T P) ≫
    (eval (A := A) T n).mapDerivedCategoryFactors.hom.app
      (((reductionModule d T).mapHomologicalComplex (.up ℤ)).obj P)
  naturality := by
    intro P Q v
    have h := (complexCounitNat (reductionModule d T) (reduction d T)
      (reductionCounit d T)).naturality v
    simp only [complexCounitNat_app] at h
    have h' := (eval (A := A) T n).mapDerivedCategoryFactors.hom.naturality
      (((reductionModule d T).mapHomologicalComplex (.up ℤ)).map v)
    dsimp only [Functor.comp_map] at h h' ⊢
    erw [← Functor.map_comp_assoc, h, Functor.map_comp, Category.assoc, h']
    simp only [Category.assoc]
    transport_rfl

private theorem evalCounit_isIso (T : Scheme.{t}) (n : ℕ)
    (P : CochainComplex (reductionModules T (exchangeConstantRing T A)) ℤ)
    (hP : proEtaleFlatRepresentatives T (exchangeConstantRing T A) P) :
    IsIso ((evalCounit d T n).app P) := by
  have : IsIso (reductionComplexCounit d T P) :=
    (reductionData d T).complexCounit_isIso P
    ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).2 hP.1)
  dsimp only [evalCounit]
  infer_instance

private def evaluatedPullIso (n : ℕ) :
    reduction d V ⋙ (eval (A := A) V n).mapDerivedCategory ⋙ pull (A := A) f ≅
      pull (A := A) f ⋙ reduction d U ⋙ (eval (A := A) U n).mapDerivedCategory :=
  Functor.isoWhiskerLeft (reduction d V)
    (AlgebraicGeometry.ProEtale.StrictTower.evalG A f n).symm ≪≫
    Functor.isoWhiskerRight (reductionPullIso d f) (eval (A := A) U n).mapDerivedCategory

private theorem evalPull_factors (n : ℕ)
    (K : CochainComplex (exchangeTowers V (exchangeConstantRing V A)) ℤ) :
    (AlgebraicGeometry.ProEtale.StrictTower.evalG A f n).inv.app
        (DerivedCategory.Q.obj K) ≫
      (eval (A := A) U n).mapDerivedCategory.map
        ((exchangeTowerModulePull f (exchangeConstantRing V A) (exchangeConstantRing U A)
          (exchangeConstantIso f A)).mapDerivedCategoryFactors.hom.app K) ≫
      (eval (A := A) U n).mapDerivedCategoryFactors.hom.app
        (((exchangeTowerModulePull f (exchangeConstantRing V A)
          (exchangeConstantRing U A) (exchangeConstantIso f A)).mapHomologicalComplex
            (.up ℤ)).obj K) =
    (pull (A := A) f).map ((eval (A := A) V n).mapDerivedCategoryFactors.hom.app K) ≫
      (proEtaleRingDerivedPullbackFactors f (exchangeConstantRing V A)
        (exchangeConstantRing U A) (exchangeConstantIso f A)).hom.app
          (((eval (A := A) V n).mapHomologicalComplex (.up ℤ)).obj K) := by
  let E := AlgebraicGeometry.ProEtale.StrictTower.evalG A f n
  have h := exactSquareFactors (eval (A := A) V n) (eval (A := A) U n)
    (exchangeTowerModulePull f (exchangeConstantRing V A) (exchangeConstantRing U A)
      (exchangeConstantIso f A))
    (proEtaleRingModulePullback f (exchangeConstantRing V A) (exchangeConstantRing U A)
      (exchangeConstantIso f A))
    (eqToIso (AlgebraicGeometry.ProEtale.StrictTower.evaluationPullback A f n)) K
  change E.hom.app (DerivedCategory.Q.obj K) ≫ _ = _ at h
  have hid : (NatTrans.mapHomologicalComplex
      (eqToIso (AlgebraicGeometry.ProEtale.StrictTower.evaluationPullback A f n)).hom
        (.up ℤ)).app K = 𝟙 _ := by
    ext i
    rfl
  erw [hid, DerivedCategory.Q.map_id, Category.comp_id] at h
  apply (cancel_epi (E.hom.app (DerivedCategory.Q.obj K))).1
  change E.hom.app _ ≫ E.inv.app _ ≫ _ = _
  rw [Iso.hom_inv_id_app_assoc]
  exact h.symm

attribute [local irreducible] AlgebraicGeometry.ProEtale.StrictTower.evalG
attribute [local implicit_reducible] AlgebraicGeometry.ProEtale.StrictTower.G
  AlgebraicGeometry.ProEtale.StrictTower.modulePullback
  AlgebraicGeometry.ProEtale.StrictTower.constantRingIso exchangeConstantIso
  proEtaleConstantComparison

/- The normalization of `reductionPullIso` on one flat representative, in the form used below.
Its instance arguments differ from those of `ReductionPullNormalized`, so this conversion is
checked once here. -/
private theorem reductionPullIso_counit_app
    (P : CochainComplex (reductionModules V (exchangeConstantRing V A)) ℤ)
    (hP : proEtaleFlatRepresentatives V (exchangeConstantRing V A) P) :
    (reductionPullIso d f).hom.app (DerivedCategory.Q.obj P) ≫
      (reduction d U).map
        ((proEtaleRingDerivedPullbackFactors f (exchangeConstantRing V A)
          (exchangeConstantRing U A) (exchangeConstantIso f A)).hom.app P) ≫
      reductionComplexCounit d U
        (((proEtaleRingModulePullback f (exchangeConstantRing V A) (exchangeConstantRing U A)
          (exchangeConstantIso f A)).mapHomologicalComplex (.up ℤ)).obj P) =
    (exchangeTowerModulePull f (exchangeConstantRing V A) (exchangeConstantRing U A)
        (exchangeConstantIso f A)).mapDerivedCategory.map
        ((reductionData d V).complexCounit P) ≫
      (exchangeTowerModulePull f (exchangeConstantRing V A) (exchangeConstantRing U A)
        (exchangeConstantIso f A)).mapDerivedCategoryFactors.hom.app
          (((reductionModule d V).mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex (ordinaryReductionPullIso d f) (.up ℤ)).hom.app P) :=
  (reductionPullIso_existsUnique d f).choose_spec.1 P
    ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).2 hP.1)

private theorem evaluatedPullIso_counit (n : ℕ)
    (P : CochainComplex (reductionModules V (exchangeConstantRing V A)) ℤ)
    (hP : proEtaleFlatRepresentatives V (exchangeConstantRing V A) P) :
    let L := (proEtaleRingModulePullback f (exchangeConstantRing V A)
      (exchangeConstantRing U A) (exchangeConstantIso f A)).mapHomologicalComplex (.up ℤ)
    (evaluatedPullIso d f n).hom.app (DerivedCategory.Q.obj P) ≫
      (reduction d U ⋙ (eval (A := A) U n).mapDerivedCategory).map
        ((proEtaleRingDerivedPullbackFactors f (exchangeConstantRing V A)
          (exchangeConstantRing U A) (exchangeConstantIso f A)).hom.app P) ≫
      (evalCounit d U n).app (L.obj P) =
    (pull (A := A) f).map ((evalCounit d V n).app P) ≫
      (proEtaleRingDerivedPullbackFactors f (exchangeConstantRing V A)
        (exchangeConstantRing U A) (exchangeConstantIso f A)).hom.app
          (((level d V n).mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex (levelPullIso d f n) (.up ℤ)).hom.app P) := by
  have hn := reductionPullIso_counit_app d f P hP
  rw [← Category.assoc] at hn
  let E := eval (A := A) U n
  let K := ((reductionModule d V).mapHomologicalComplex (.up ℤ)).obj P
  have he := E.mapDerivedCategoryFactors.hom.naturality
    ((NatIso.mapHomologicalComplex (ordinaryReductionPullIso d f) (.up ℤ)).hom.app P)
  have hG := (AlgebraicGeometry.ProEtale.StrictTower.evalG A f n).inv.naturality
    (reductionComplexCounit d V P)
  dsimp only [Functor.comp_map] at he hG
  dsimp only [evaluatedPullIso, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, NatTrans.comp_app, Functor.associator_hom_app,
    Functor.associator_inv_app, evalCounit, Functor.comp_map]
  simp only [Category.assoc]
  erw [← E.mapDerivedCategory.map_comp_assoc, ← E.mapDerivedCategory.map_comp_assoc,
    hn, E.mapDerivedCategory.map_comp, E.mapDerivedCategory.map_comp]
  simp only [Category.assoc]
  erw [he, ← reassoc_of% hG]
  erw [reassoc_of% (evalPull_factors (A := A) f n K)]
  simp only [Functor.map_comp, Category.assoc]
  rfl

private theorem evaluatedScalarIso (T : Scheme.{t}) (n : ℕ) :
    ∃ e : reduction d T ⋙ (eval (A := A) T n).mapDerivedCategory ≅
        proEtaleRingDerivedExtension (quotient d T n) ⋙
          (DerivedScalarMate.restriction (quotient d T n)).mapDerivedCategory,
      ∀ (P : CochainComplex (reductionModules T (exchangeConstantRing T A)) ℤ)
        (_hP : proEtaleFlatRepresentatives T (exchangeConstantRing T A) P),
        e.hom.app (DerivedCategory.Q.obj P) ≫
          (DerivedScalarMate.scalarCounit (quotient d T n)).app P =
            (evalCounit d T n).app P := by
  let PR := proEtaleFlatRepresentatives T (exchangeConstantRing T A)
  let L := PR.ι ⋙ DerivedCategory.Q
  let α := Functor.whiskerLeft PR.ι (evalCounit d T n)
  let β := Functor.whiskerLeft PR.ι
    (DerivedScalarMate.scalarCounit (quotient d T n))
  have (P : PR.FullSubcategory) : IsIso (α.app P) :=
    evalCounit_isIso d T n P.obj P.property
  have (P : PR.FullSubcategory) : IsIso (β.app P) :=
    DerivedScalarMate.scalarCounit_isIso _ P.obj P.property
  have : IsIso α := NatIso.isIso_of_isIso_app _
  have : IsIso β := NatIso.isIso_of_isIso_app _
  let c : L ⋙ (reduction d T ⋙ (eval (A := A) T n).mapDerivedCategory) ≅
      L ⋙ (proEtaleRingDerivedExtension (quotient d T n) ⋙
        (DerivedScalarMate.restriction (quotient d T n)).mapDerivedCategory) :=
    asIso α ≪≫ (asIso β).symm
  obtain ⟨ff₂⟩ := DerivedScalarMate.representativeWhiskering T (exchangeConstantRing T A)
  obtain ⟨ff⟩ := DerivedScalarMate.unaryWhiskering L ff₂
  let e := ff.preimageIso c
  refine ⟨e, ?_⟩
  intro P hP
  let X : PR.FullSubcategory := ⟨P, hP⟩
  have he : e.hom.app (L.obj X) = c.hom.app X :=
    congr_app (ff.map_preimage c.hom) X
  change e.hom.app (L.obj X) ≫ β.app X = α.app X
  rw [he]
  change ((asIso α).hom.app X ≫ (asIso β).inv.app X) ≫
    (asIso β).hom.app X = (asIso α).hom.app X
  erw [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]

private def evaluatedTensorIso (T : Scheme.{t}) (n : ℕ)
    (a : ProEtaleTensorModel T (exchangeConstantRing T A))
    (F : CochainComplex (reductionModules T (exchangeConstantRing T A)) ℤ)
    (q : F ⟶ DerivedScalarMate.coefficientComplex (quotient d T n)) (hq : QuasiIso q) :
    reduction d T ⋙ (eval (A := A) T n).mapDerivedCategory ≅
      (Functor.curryObj a.tensor).flip.obj (DerivedCategory.Q.obj F) := by
  have : IsIso (DerivedCategory.Q.map q) :=
    Localization.inverts DerivedCategory.Q (HomologicalComplex.quasiIso _ _) q hq
  exact (evaluatedScalarIso d T n).choose ≪≫
    DerivedScalarMate.derivedTensorIso (quotient d T n) a ≪≫
    (Functor.curryObj a.tensor).flip.mapIso (asIso (DerivedCategory.Q.map q)).symm

private theorem evaluatedTensorIso_normalization (T : Scheme.{t}) (n : ℕ)
    (a : ProEtaleTensorModel T (exchangeConstantRing T A))
    (P F : CochainComplex (reductionModules T (exchangeConstantRing T A)) ℤ)
    (hP : proEtaleFlatRepresentatives T (exchangeConstantRing T A) P)
    (hF : proEtaleFlatRepresentatives T (exchangeConstantRing T A) F)
    (q : F ⟶ DerivedScalarMate.coefficientComplex (quotient d T n)) (hq : QuasiIso q) :
    a.representative.hom.app (⟨P, hP⟩, ⟨F, hF⟩) ≫
      (evaluatedTensorIso d T n a F q hq).inv.app (DerivedCategory.Q.obj P) ≫
      (evalCounit d T n).app P =
    DerivedCategory.Q.map
      (HomologicalComplex.mapBifunctorMap (𝟙 P) q
        (proEtaleOrdinaryTensor T (exchangeConstantRing T A)) (.up ℤ) ≫
          (DerivedScalarMate.ordinaryComplexIso (quotient d T n) P).inv) := by
  have : IsIso (DerivedCategory.Q.map q) :=
    Localization.inverts DerivedCategory.Q (HomologicalComplex.quasiIso _ _) q hq
  have he := (evaluatedScalarIso d T n).choose_spec P hP
  have hn := (Classical.choose_spec
    (DerivedScalarMate.derivedTensorIso_existsUnique (quotient d T n) a).exists)
      P F hP hF q hq
  have hc : (evaluatedScalarIso d T n).choose.inv.app (DerivedCategory.Q.obj P) ≫
      (evalCounit d T n).app P =
        (DerivedScalarMate.scalarCounit (quotient d T n)).app P := by
    rw [← he, Iso.inv_hom_id_app_assoc]
  dsimp only [evaluatedTensorIso, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
    Functor.mapIso_hom, asIso_hom]
  simp only [Category.assoc]
  rw [hc]
  exact hn

private def quotientCoefficientPullback (n : ℕ) :
    (proEtaleRingModulePullback f (exchangeConstantRing V A)
      (exchangeConstantRing U A) (exchangeConstantIso f A)).obj
        (DerivedScalarMate.coefficient (quotient d V n)) ≅
          DerivedScalarMate.coefficient (quotient d U n) :=
  (@asIso _ _ _ _
    (proEtaleRingRestrictionPullbackInv f (exchangeConstantRing V A) (d.finiteRing V n)
      (exchangeConstantRing U A) (d.finiteRing U n) (quotient d V n) (quotient d U n)
      (exchangeConstantIso f A) (d.finiteRingIso f n) (quotient_comm d f n))
    (proEtaleRingRestrictionPullbackInv_isIso f _ _ _ _ _ _ _ _ _)).app
      (SheafOfModules.unit ((adicLisseForget V).obj (d.finiteRing V n))) ≪≫
    (DerivedScalarMate.restriction (quotient d U n)).mapIso
      (Classical.choose (proEtaleProjectionUnit_existsUnique f (d.finiteRing V n)
        (d.finiteRing U n) (d.finiteRingIso f n)).exists)

private def quotientCoefficientComplexPullback (n : ℕ) :
    ((proEtaleRingModulePullback f (exchangeConstantRing V A)
      (exchangeConstantRing U A) (exchangeConstantIso f A)).mapHomologicalComplex
        (.up ℤ)).obj (DerivedScalarMate.coefficientComplex (quotient d V n)) ≅
      DerivedScalarMate.coefficientComplex (quotient d U n) :=
  ((HomologicalComplex.singleMapHomologicalComplex
    (proEtaleRingModulePullback f (exchangeConstantRing V A)
      (exchangeConstantRing U A) (exchangeConstantIso f A))
    (.up ℤ) 0).app (DerivedScalarMate.coefficient (quotient d V n))) ≪≫
    (CochainComplex.singleFunctor _ (0 : ℤ)).mapIso
      (quotientCoefficientPullback d f n)

private theorem quotientCoefficientPullback_unit (n : ℕ)
    (W : V.ProEtᵒᵖ) (s : (d.finiteRing V n).obj.obj W) :
    (quotientCoefficientPullback d f n).hom.val.app ((proEtaleBaseChange f).op.obj W)
      (((proEtaleRingModuleAdjunction f (exchangeConstantRing V A)
        (exchangeConstantRing U A) (exchangeConstantIso f A)).unit.app
          (DerivedScalarMate.coefficient (quotient d V n))).val.app W s) =
      (proEtaleRingDirectImageMap f (d.finiteRing V n) (d.finiteRing U n)
        (d.finiteRingIso f n)).hom.app W s := by
  have h := congrArg (fun k ↦ k.val.app W s)
    (DerivedScalarMate.projectionUnit_homEquiv f (d.finiteRing V n)
      (d.finiteRing U n) (d.finiteRingIso f n))
  rw [Adjunction.homEquiv_unit] at h
  unfold quotientCoefficientPullback
  dsimp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, asIso_hom]
  change (Classical.choose
    (proEtaleProjectionUnit_existsUnique f (d.finiteRing V n) (d.finiteRing U n)
      (d.finiteRingIso f n)).exists).hom.val.app _
      (((proEtaleRingRestrictionPullbackInv f (exchangeConstantRing V A) (d.finiteRing V n)
        (exchangeConstantRing U A) (d.finiteRing U n) (quotient d V n) (quotient d U n)
        (exchangeConstantIso f A) (d.finiteRingIso f n) (quotient_comm d f n)).app
        (SheafOfModules.unit _)).val.app _ _) = _
  rw [restrictionPullback_unit]
  exact h

private theorem quotientOrdinarySquare (n : ℕ)
    (M : reductionModules V (exchangeConstantRing V A)) :
    (proEtaleRingModulePullback f (exchangeConstantRing V A)
      (exchangeConstantRing U A) (exchangeConstantIso f A)).map
        ((DerivedScalarMate.ordinaryTensorIso (quotient d V n)).hom.app M) ≫
      (proEtaleOrdinaryTensorPullback f (exchangeConstantRing V A)
        (exchangeConstantRing U A) (exchangeConstantIso f A) M
          (DerivedScalarMate.coefficient (quotient d V n))).hom ≫
      ((proEtaleOrdinaryTensor U (exchangeConstantRing U A)).obj
        ((proEtaleRingModulePullback f (exchangeConstantRing V A)
          (exchangeConstantRing U A) (exchangeConstantIso f A)).obj M)).map
            (quotientCoefficientPullback d f n).hom =
      (levelPullIso d f n).hom.app M ≫
        (DerivedScalarMate.ordinaryTensorIso (quotient d U n)).hom.app
          ((proEtaleRingModulePullback f (exchangeConstantRing V A)
            (exchangeConstantRing U A) (exchangeConstantIso f A)).obj M) := by
  let adj := proEtaleRingModuleAdjunction f (exchangeConstantRing V A)
    (exchangeConstantRing U A) (exchangeConstantIso f A)
  apply (adj.homEquiv _ _).injective
  apply AlgebraicGeometry.ProEtale.StrictTower.ConstantNormalization.level_hom_ext
    V (quotient d V n) M
  intro W s x
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  let W' := (proEtaleBaseChange f).op.obj W
  have hn := congrArg (fun k ↦ k.val.app W
    (reductionTensorSection V (quotient d V n) M W s x))
      (adj.unit.naturality
        ((DerivedScalarMate.ordinaryTensorIso (quotient d V n)).hom.app M))
  have ht := (Classical.choose_spec
    (proEtaleOrdinaryTensorPullback_existsUnique f (exchangeConstantRing V A)
      (exchangeConstantRing U A) (exchangeConstantIso f A)).exists).2 M
        (DerivedScalarMate.coefficient (quotient d V n)) W.unop x s
  dsimp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
  let L := proEtaleRingModulePullback f (exchangeConstantRing V A)
    (exchangeConstantRing U A) (exchangeConstantIso f A)
  let cV := DerivedScalarMate.coefficient (quotient d V n)
  let eV := (DerivedScalarMate.ordinaryTensorIso (quotient d V n)).hom.app M
  let eU := (DerivedScalarMate.ordinaryTensorIso (quotient d U n)).hom.app (L.obj M)
  let μ := (proEtaleOrdinaryTensorPullback f (exchangeConstantRing V A)
    (exchangeConstantRing U A) (exchangeConstantIso f A) M cV).hom
  let k := ((proEtaleOrdinaryTensor U (exchangeConstantRing U A)).obj (L.obj M)).map
    (quotientCoefficientPullback d f n).hom
  change k.val.app W' (μ.val.app W' ((L.map eV).val.app W'
    ((adj.unit.app ((level d V n).obj M)).val.app W
      (reductionTensorSection V (quotient d V n) M W s x)))) =
    eU.val.app W' (((levelPullIso d f n).hom.app M).val.app W'
      ((adj.unit.app ((level d V n).obj M)).val.app W
        (reductionTensorSection V (quotient d V n) M W s x)))
  change (adj.unit.app _).val.app W
      (eV.val.app W (reductionTensorSection V (quotient d V n) M W s x)) =
    (L.map eV).val.app W' ((adj.unit.app ((level d V n).obj M)).val.app W
      (reductionTensorSection V (quotient d V n) M W s x)) at hn
  rw [← hn]
  dsimp only [eV, eU, μ, k]
  rw [DerivedScalarMate.ordinaryTensorIso_section]
  erw [ht]
  simp only [proEtaleOrdinaryTensor, MonoidalCategory.curriedTensor_obj_map,
    ← MonoidalCategory.id_tensorHom]
  have hm := proEtaleTensorPair_tensorHom U (exchangeConstantRing U A)
    (𝟙 ((proEtaleRingModulePullback f (exchangeConstantRing V A)
      (exchangeConstantRing U A) (exchangeConstantIso f A)).obj M))
      (quotientCoefficientPullback d f n).hom W'
        ((adj.unit.app M).val.app W x)
        ((adj.unit.app (DerivedScalarMate.coefficient (quotient d V n))).val.app W s)
  erw [hm]
  rw [quotientCoefficientPullback_unit]
  rw [levelPullIso_tensor, DerivedScalarMate.ordinaryTensorIso_section]
  rfl

private theorem quotientOrdinaryComplexSquare (n : ℕ)
    (P : CochainComplex (reductionModules V (exchangeConstantRing V A)) ℤ) :
    let L := (proEtaleRingModulePullback f (exchangeConstantRing V A)
      (exchangeConstantRing U A) (exchangeConstantIso f A)).mapHomologicalComplex (.up ℤ)
    (NatIso.mapHomologicalComplex (levelPullIso d f n) (.up ℤ)).hom.app P ≫
      (DerivedScalarMate.ordinaryComplexIso (quotient d U n) (L.obj P)).hom =
    L.map (DerivedScalarMate.ordinaryComplexIso (quotient d V n) P).hom ≫
      tensorOnePullback f (exchangeConstantRing V A) (exchangeConstantRing U A)
        (exchangeConstantIso f A) (DerivedScalarMate.coefficient (quotient d V n))
          (DerivedScalarMate.coefficient (quotient d U n))
            (quotientCoefficientPullback d f n) P := by
  let FA := proEtaleRingModulePullback f (exchangeConstantRing V A)
    (exchangeConstantRing U A) (exchangeConstantIso f A)
  let L := FA.mapHomologicalComplex (.up ℤ)
  let TV := proEtaleOrdinaryTensor V (exchangeConstantRing V A)
  let TU := proEtaleOrdinaryTensor U (exchangeConstantRing U A)
  let CV := DerivedScalarMate.coefficient (quotient d V n)
  let CU := DerivedScalarMate.coefficient (quotient d U n)
  let sy := CochainComplex.mapBifunctorSingle₂Iso TV CV P
  let sx := CochainComplex.mapBifunctorSingle₂Iso TU CU (L.obj P)
  let j := tensorOnePullback f _ _ (exchangeConstantIso f A) CV CU
    (quotientCoefficientPullback d f n) P
  have hm : (NatIso.mapHomologicalComplex (levelPullIso d f n) (.up ℤ)).hom.app P ≫
      (Functor.mapHomologicalComplexCompIso
        (DerivedScalarMate.ordinaryTensorIso (quotient d U n)) (.up ℤ)).hom.app (L.obj P) =
    L.map ((Functor.mapHomologicalComplexCompIso
      (DerivedScalarMate.ordinaryTensorIso (quotient d V n)) (.up ℤ)).hom.app P) ≫
        L.map sy.inv ≫ j ≫ sx.hom := by
    apply HomologicalComplex.hom_ext
    intro i
    have hs := tensorOnePullback_single_f f (exchangeConstantRing V A)
      (exchangeConstantRing U A) (exchangeConstantIso f A) CV CU
        (quotientCoefficientPullback d f n) P i
    dsimp only [Functor.mapHomologicalComplexCompIso, NatIso.mapHomologicalComplex_hom_app_f,
      HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f]
    have h := quotientOrdinarySquare d f n (P.X i)
    dsimp only [j, L, FA, sy, sx, TV, TU, CV, CU] at hs
    rw [← Category.assoc, ← Category.assoc]
    exact h.symm.trans (congrArg
      (fun z ↦ FA.map ((DerivedScalarMate.ordinaryTensorIso
        (quotient d V n)).hom.app (P.X i)) ≫ z) hs.symm)
  unfold DerivedScalarMate.ordinaryComplexIso
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom]
  erw [L.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% hm]
  change L.map ((Functor.mapHomologicalComplexCompIso
      (DerivedScalarMate.ordinaryTensorIso (quotient d V n)) (.up ℤ)).hom.app P) ≫
      L.map sy.inv ≫ j ≫ sx.hom ≫ sx.inv =
    L.map ((Functor.mapHomologicalComplexCompIso
      (DerivedScalarMate.ordinaryTensorIso (quotient d V n)) (.up ℤ)).hom.app P) ≫
      L.map sy.inv ≫ j
  erw [sx.hom_inv_id, Category.comp_id]

private theorem uncurry_map_id_left {C D E : Type*}
    [Category C] [Category D] [Category E] (H : C ⥤ D ⥤ E)
    (X : C) {Y Y' : D} (v : Y ⟶ Y') :
    (Functor.uncurry.obj H).map (Prod.mkHom (𝟙 X) v) = (H.obj X).map v := by
  change (H.map (𝟙 X)).app Y ≫ (H.obj X).map v = _
  rw [H.map_id, NatTrans.id_app, Category.id_comp]

private theorem quotientAugmentedSquare (n : ℕ)
    (P F : CochainComplex (reductionModules V (exchangeConstantRing V A)) ℤ)
    (q : F ⟶ DerivedScalarMate.coefficientComplex (quotient d V n)) :
    let L := (proEtaleRingModulePullback f (exchangeConstantRing V A)
      (exchangeConstantRing U A) (exchangeConstantIso f A)).mapHomologicalComplex (.up ℤ)
    (proEtaleTensorPullbackTotalIso f (exchangeConstantRing V A)
      (exchangeConstantRing U A) (exchangeConstantIso f A) P F).inv ≫
      HomologicalComplex.mapBifunctorMap (𝟙 (L.obj P))
        (L.map q ≫ (quotientCoefficientComplexPullback d f n).hom)
        (proEtaleOrdinaryTensor U (exchangeConstantRing U A)) (.up ℤ) ≫
      (DerivedScalarMate.ordinaryComplexIso (quotient d U n) (L.obj P)).inv =
    L.map (HomologicalComplex.mapBifunctorMap (𝟙 P) q
      (proEtaleOrdinaryTensor V (exchangeConstantRing V A)) (.up ℤ) ≫
        (DerivedScalarMate.ordinaryComplexIso (quotient d V n) P).inv) ≫
      (NatIso.mapHomologicalComplex (levelPullIso d f n) (.up ℤ)).hom.app P := by
  let L := (proEtaleRingModulePullback f (exchangeConstantRing V A)
    (exchangeConstantRing U A) (exchangeConstantIso f A)).mapHomologicalComplex (.up ℤ)
  let TV := Functor.uncurry.obj
    ((proEtaleOrdinaryTensor V (exchangeConstantRing V A)).map₂HomologicalComplex
      (.up ℤ) (.up ℤ) (.up ℤ))
  let TU := Functor.uncurry.obj
    ((proEtaleOrdinaryTensor U (exchangeConstantRing U A)).map₂HomologicalComplex
      (.up ℤ) (.up ℤ) (.up ℤ))
  let CV := DerivedScalarMate.coefficientComplex (quotient d V n)
  let k := quotientCoefficientComplexPullback d f n
  let j := tensorOnePullback f (exchangeConstantRing V A) (exchangeConstantRing U A)
    (exchangeConstantIso f A) (DerivedScalarMate.coefficient (quotient d V n))
      (DerivedScalarMate.coefficient (quotient d U n))
        (quotientCoefficientPullback d f n) P
  obtain ⟨_, _, e, he⟩ := proEtaleTensorPullbackDescentData f (exchangeConstantRing V A)
    (exchangeConstantRing U A) (exchangeConstantIso f A)
  have hn := e.inv.naturality (Prod.mkHom (𝟙 P) q)
  rw [he, he] at hn
  change L.map (TV.map (Prod.mkHom (𝟙 P) q)) ≫
      (proEtaleTensorPullbackTotalIso f _ _ (exchangeConstantIso f A) P CV).inv =
    (proEtaleTensorPullbackTotalIso f _ _ (exchangeConstantIso f A) P F).inv ≫
      TU.map (Prod.mkHom (L.map (𝟙 P)) (L.map q)) at hn
  have hcoef : HomologicalComplex.mapBifunctorMap (𝟙 (L.obj P)) k.hom
      (proEtaleOrdinaryTensor U (exchangeConstantRing U A)) (.up ℤ) =
      TU.map (Prod.mkHom (𝟙 (L.obj P)) k.hom) :=
    (uncurry_map_id_left
      ((proEtaleOrdinaryTensor U (exchangeConstantRing U A)).map₂HomologicalComplex
        (.up ℤ) (.up ℤ) (.up ℤ)) (L.obj P) k.hom).symm
  have hTV : TV.map (Prod.mkHom (𝟙 P) q) =
      HomologicalComplex.mapBifunctorMap (𝟙 P) q
        (proEtaleOrdinaryTensor V (exchangeConstantRing V A)) (.up ℤ) :=
    uncurry_map_id_left
      ((proEtaleOrdinaryTensor V (exchangeConstantRing V A)).map₂HomologicalComplex
        (.up ℤ) (.up ℤ) (.up ℤ)) P q
  have hTU : TU.map (Prod.mkHom (𝟙 (L.obj P)) (L.map q ≫ k.hom)) =
      HomologicalComplex.mapBifunctorMap (𝟙 (L.obj P)) (L.map q ≫ k.hom)
        (proEtaleOrdinaryTensor U (exchangeConstantRing U A)) (.up ℤ) :=
    uncurry_map_id_left
      ((proEtaleOrdinaryTensor U (exchangeConstantRing U A)).map₂HomologicalComplex
        (.up ℤ) (.up ℤ) (.up ℤ)) (L.obj P) (L.map q ≫ k.hom)
  have ha : L.map (HomologicalComplex.mapBifunctorMap (𝟙 P) q
      (proEtaleOrdinaryTensor V (exchangeConstantRing V A)) (.up ℤ)) ≫ j =
      (proEtaleTensorPullbackTotalIso f _ _ (exchangeConstantIso f A) P F).inv ≫
        HomologicalComplex.mapBifunctorMap (𝟙 (L.obj P)) (L.map q ≫ k.hom)
          (proEtaleOrdinaryTensor U (exchangeConstantRing U A)) (.up ℤ) := by
    dsimp only [j, tensorOnePullback]
    erw [hcoef, ← Category.assoc, ← hTV, hn, Category.assoc,
      ← TU.map_comp, ← hTU]
    congr 2
    apply Prod.ext
    · change L.map (𝟙 P) ≫ 𝟙 (L.obj P) = 𝟙 (L.obj P)
      rw [L.map_id, Category.id_comp]
    · rfl
  have hj : j ≫ (DerivedScalarMate.ordinaryComplexIso
      (quotient d U n) (L.obj P)).inv =
      L.map (DerivedScalarMate.ordinaryComplexIso (quotient d V n) P).inv ≫
        (NatIso.mapHomologicalComplex (levelPullIso d f n) (.up ℤ)).hom.app P := by
    apply (cancel_epi
      (L.map (DerivedScalarMate.ordinaryComplexIso (quotient d V n) P).hom)).1
    rw [← Category.assoc, ← quotientOrdinaryComplexSquare d f n P]
    change _ ≫
        (DerivedScalarMate.ordinaryComplexIso (quotient d U n) (L.obj P)).hom ≫
        (DerivedScalarMate.ordinaryComplexIso (quotient d U n) (L.obj P)).inv = _
    erw [Iso.hom_inv_id, Category.comp_id, (L.mapIso
      (DerivedScalarMate.ordinaryComplexIso (quotient d V n) P)).hom_inv_id_assoc]
  dsimp only
  rw [← reassoc_of% ha, hj, L.map_comp]
  simp only [Category.assoc]

private theorem comparisonOnRepresentatives (n : ℕ)
    (a : ProEtaleTensorModel V (exchangeConstantRing V A))
    (b : ProEtaleTensorModel U (exchangeConstantRing U A))
    (P F : CochainComplex (reductionModules V (exchangeConstantRing V A)) ℤ)
    (hP : proEtaleFlatRepresentatives V (exchangeConstantRing V A) P)
    (hF : proEtaleFlatRepresentatives V (exchangeConstantRing V A) F)
    (q : F ⟶ DerivedScalarMate.coefficientComplex (quotient d V n)) (hq : QuasiIso q) :
    let L := (proEtaleRingModulePullback f (exchangeConstantRing V A)
      (exchangeConstantRing U A) (exchangeConstantIso f A)).mapHomologicalComplex (.up ℤ)
    let r := L.map q ≫ (quotientCoefficientComplexPullback d f n).hom
    ∃ hr : QuasiIso r,
      (pull (A := A) f).map ((evaluatedTensorIso d V n a F q hq).hom.app
        (DerivedCategory.Q.obj P)) ≫
        (proEtaleCanonicalTensorComparison f (exchangeConstantRing V A)
          (exchangeConstantRing U A) (exchangeConstantIso f A) a b).hom.app
            (DerivedCategory.Q.obj P, DerivedCategory.Q.obj F) ≫
        b.tensor.map (Prod.mkHom
          ((proEtaleRingDerivedPullbackFactors f (exchangeConstantRing V A)
            (exchangeConstantRing U A) (exchangeConstantIso f A)).hom.app P)
          ((proEtaleRingDerivedPullbackFactors f (exchangeConstantRing V A)
            (exchangeConstantRing U A) (exchangeConstantIso f A)).hom.app F)) =
      (evaluatedPullIso d f n).hom.app (DerivedCategory.Q.obj P) ≫
        (reduction d U ⋙ (eval (A := A) U n).mapDerivedCategory).map
          ((proEtaleRingDerivedPullbackFactors f (exchangeConstantRing V A)
            (exchangeConstantRing U A) (exchangeConstantIso f A)).hom.app P) ≫
        (evaluatedTensorIso d U n b (L.obj F) r hr).hom.app
          (DerivedCategory.Q.obj (L.obj P)) := by
  classical
  dsimp only
  let L := (proEtaleRingModulePullback f (exchangeConstantRing V A)
    (exchangeConstantRing U A) (exchangeConstantIso f A)).mapHomologicalComplex (.up ℤ)
  let D := pull (A := A) f
  let δ := proEtaleRingDerivedPullbackFactors f (exchangeConstantRing V A)
    (exchangeConstantRing U A) (exchangeConstantIso f A)
  let μ := proEtaleCanonicalTensorComparison f (exchangeConstantRing V A)
    (exchangeConstantRing U A) (exchangeConstantIso f A) a b
  let r := L.map q ≫ (quotientCoefficientComplexPullback d f n).hom
  have : QuasiIso q := hq
  have hr : QuasiIso r := by dsimp only [r, L]; infer_instance
  refine ⟨hr, ?_⟩
  let eV := evaluatedTensorIso d V n a F q hq
  let eU := evaluatedTensorIso d U n b (L.obj F) r hr
  obtain ⟨hP', hF', hs⟩ :=
    (Classical.choose_spec (proEtaleCanonicalTensorPullback f (exchangeConstantRing V A)
      (exchangeConstantRing U A) (exchangeConstantIso f A) a b).2.exists) P F hP hF
  let αV := (evalCounit d V n).app P
  let αU := (evalCounit d U n).app (L.obj P)
  let v := HomologicalComplex.mapBifunctorMap (𝟙 P) q
    (proEtaleOrdinaryTensor V (exchangeConstantRing V A)) (.up ℤ) ≫
      (DerivedScalarMate.ordinaryComplexIso (quotient d V n) P).inv
  let u := HomologicalComplex.mapBifunctorMap (𝟙 (L.obj P)) r
    (proEtaleOrdinaryTensor U (exchangeConstantRing U A)) (.up ℤ) ≫
      (DerivedScalarMate.ordinaryComplexIso (quotient d U n) (L.obj P)).inv
  let β := (NatIso.mapHomologicalComplex (levelPullIso d f n) (.up ℤ)).hom.app P
  let τ := (proEtaleTensorPullbackTotalIso f (exchangeConstantRing V A)
    (exchangeConstantRing U A) (exchangeConstantIso f A) P F).inv
  have hv : a.representative.hom.app (⟨P, hP⟩, ⟨F, hF⟩) ≫
      eV.inv.app (DerivedCategory.Q.obj P) ≫ αV = DerivedCategory.Q.map v :=
    evaluatedTensorIso_normalization d V n a P F hP hF q hq
  have hu : b.representative.hom.app (⟨L.obj P, hP'⟩, ⟨L.obj F, hF'⟩) ≫
      eU.inv.app (DerivedCategory.Q.obj (L.obj P)) ≫ αU = DerivedCategory.Q.map u :=
    evaluatedTensorIso_normalization d U n b _ _ hP' hF' r hr
  have hτ : τ ≫ u = L.map v ≫ β := quotientAugmentedSquare d f n P F q
  have hδ := δ.hom.naturality v
  change D.map (DerivedCategory.Q.map v) ≫ δ.hom.app _ =
    δ.hom.app _ ≫ DerivedCategory.Q.map (L.map v) at hδ
  have hα := evaluatedPullIso_counit d f n P hP
  have : IsIso αU := evalCounit_isIso d U n (L.obj P) hP'
  apply (cancel_mono (eU.inv.app (DerivedCategory.Q.obj (L.obj P)) ≫ αU)).1
  apply (cancel_epi (D.map
    (a.representative.hom.app (⟨P, hP⟩, ⟨F, hF⟩) ≫
      eV.inv.app (DerivedCategory.Q.obj P)))).1
  change D.map (_ ≫ eV.inv.app _) ≫
      (D.map (eV.hom.app _) ≫ μ.hom.app _ ≫ b.tensor.map _) ≫
        (eU.inv.app _ ≫ αU) =
    D.map (_ ≫ eV.inv.app _) ≫
      ((evaluatedPullIso d f n).hom.app _ ≫ _ ≫ eU.hom.app _) ≫
        (eU.inv.app _ ≫ αU)
  have hc : D.map (eV.inv.app (DerivedCategory.Q.obj P)) ≫
      D.map (eV.hom.app (DerivedCategory.Q.obj P)) = 𝟙 _ := by
    rw [← D.map_comp, Iso.inv_hom_id_app, D.map_id]
  simp only [D.map_comp, Category.assoc, Iso.hom_inv_id_app_assoc]
  erw [reassoc_of% hc]
  calc
    D.map (a.representative.hom.app (⟨P, hP⟩, ⟨F, hF⟩)) ≫ μ.hom.app _ ≫
        b.tensor.map _ ≫ eU.inv.app _ ≫ αU =
      δ.hom.app _ ≫ DerivedCategory.Q.map τ ≫
        b.representative.hom.app (⟨L.obj P, hP'⟩, ⟨L.obj F, hF'⟩) ≫
        eU.inv.app _ ≫ αU := by
      erw [reassoc_of% hs]
      rfl
    _ = δ.hom.app _ ≫ DerivedCategory.Q.map (τ ≫ u) := by
      erw [hu]
      simp only [u, DerivedCategory.Q.map_comp]
    _ = D.map (DerivedCategory.Q.map v) ≫ δ.hom.app _ ≫
        DerivedCategory.Q.map β := by
      rw [hτ, DerivedCategory.Q.map_comp, ← reassoc_of% hδ]
      rfl
    _ = D.map (a.representative.hom.app (⟨P, hP⟩, ⟨F, hF⟩)) ≫
        D.map (eV.inv.app _) ≫
        (evaluatedPullIso d f n).hom.app _ ≫ _ ≫ αU := by
      rw [← hv, D.map_comp, D.map_comp]
      simp only [Category.assoc]
      erw [hα]
      rfl

/-- Evaluated reduction is tensor by any flat K-flat resolution of the constant quotient,
and its specified pullback square is the canonical tensor square. This statement makes
no finite-support or finite-projectivity assumption on the coefficient resolution. -/
theorem constantQuotientTensorComparison (n : ℕ)
    (F : CochainComplex (reductionModules V (exchangeConstantRing V A)) ℤ)
    (hF : proEtaleFlatRepresentatives V (exchangeConstantRing V A) F)
    (q : F ⟶ (CochainComplex.singleFunctor _ 0).obj
      ((adicLisseConstantModules V A).obj (ModuleCat.of A (A ⧸ d.ideal ^ (n + 1)))))
    (hq : QuasiIso q) :
    ∃ (a : ProEtaleTensorModel V (exchangeConstantRing V A))
      (b : ProEtaleTensorModel U (exchangeConstantRing U A))
      (eV : reduction d V ⋙
        ((CategoryTheory.evaluation ℕᵒᵖ
          (reductionModules V (exchangeConstantRing V A))).obj (op n)).mapDerivedCategory ≅
        (Functor.curryObj a.tensor).flip.obj (DerivedCategory.Q.obj F))
      (eU : reduction d U ⋙
        ((CategoryTheory.evaluation ℕᵒᵖ
          (reductionModules U (exchangeConstantRing U A))).obj (op n)).mapDerivedCategory ≅
        (Functor.curryObj b.tensor).flip.obj ((pull (A := A) f).obj
          (DerivedCategory.Q.obj F))),
      ∀ M : D (A := A) V,
        (pull (A := A) f).map (eV.hom.app M) ≫
          (proEtaleCanonicalTensorComparison f (exchangeConstantRing V A)
            (exchangeConstantRing U A) (exchangeConstantIso f A) a b).hom.app
              (M, DerivedCategory.Q.obj F) =
        (AlgebraicGeometry.ProEtale.StrictTower.evalG A f n).inv.app
            ((reduction d V).obj M) ≫
          ((CategoryTheory.evaluation ℕᵒᵖ
            (reductionModules U (exchangeConstantRing U A))).obj (op n)).mapDerivedCategory.map
              ((reductionPullIso d f).hom.app M) ≫
            eU.hom.app ((pull (A := A) f).obj M) := by
  classical
  obtain ⟨a⟩ := tensorModel_exists V (exchangeConstantRing V A)
  obtain ⟨b⟩ := tensorModel_exists U (exchangeConstantRing U A)
  let FV := (CochainComplex.singleFunctor _ (0 : ℤ)).mapIso (quotientModuleIso d V n)
  let rV := q ≫ FV.hom
  have : QuasiIso q := hq
  have hrV : QuasiIso rV := by dsimp only [rV]; infer_instance
  let L := (proEtaleRingModulePullback f (exchangeConstantRing V A)
    (exchangeConstantRing U A) (exchangeConstantIso f A)).mapHomologicalComplex (.up ℤ)
  let rU := L.map rV ≫ (quotientCoefficientComplexPullback d f n).hom
  have : QuasiIso rV := hrV
  have hrU : QuasiIso rU := by dsimp only [rU, L]; infer_instance
  let eV := evaluatedTensorIso d V n a F rV hrV
  let eU := evaluatedTensorIso d U n b (L.obj F) rU hrU ≪≫
    (Functor.curryObj b.tensor).flip.mapIso
      ((proEtaleRingDerivedPullbackFactors f (exchangeConstantRing V A)
        (exchangeConstantRing U A) (exchangeConstantIso f A)).app F).symm
  refine ⟨a, b, eV, eU, ?_⟩
  let DP := pull (A := A) f
  let δ := proEtaleRingDerivedPullbackFactors f (exchangeConstantRing V A)
    (exchangeConstantRing U A) (exchangeConstantIso f A)
  let μ := proEtaleCanonicalTensorComparison f (exchangeConstantRing V A)
    (exchangeConstantRing U A) (exchangeConstantIso f A) a b
  let RU := reduction d U ⋙ (eval (A := A) U n).mapDerivedCategory
  let eU₀ := evaluatedTensorIso d U n b (L.obj F) rU hrU
  let lhs : (reduction d V ⋙ (eval (A := A) V n).mapDerivedCategory) ⋙ DP ⟶
      DP ⋙ (Functor.curryObj b.tensor).flip.obj (DP.obj (DerivedCategory.Q.obj F)) :=
    Functor.whiskerRight eV.hom DP ≫
      { app := fun M ↦ μ.hom.app (M, DerivedCategory.Q.obj F)
        naturality := by
          intro M N z
          have hz := μ.hom.naturality (Prod.mkHom z (𝟙 (DerivedCategory.Q.obj F)))
          dsimp only [Functor.comp_map, Functor.prod_map] at hz
          erw [DP.map_id] at hz
          simpa only [Functor.comp_map, Functor.flip_obj_map, Functor.curryObj] using hz }
  let rhs : (reduction d V ⋙ (eval (A := A) V n).mapDerivedCategory) ⋙ DP ⟶
      DP ⋙ (Functor.curryObj b.tensor).flip.obj (DP.obj (DerivedCategory.Q.obj F)) :=
    (evaluatedPullIso d f n).hom ≫ Functor.whiskerLeft DP eU.hom
  have heq : lhs = rhs := by
    let PR := proEtaleFlatRepresentatives V (exchangeConstantRing V A)
    obtain ⟨_, ⟨ff₂⟩, _⟩ := proEtaleTensorPullbackDescentData f (exchangeConstantRing V A)
      (exchangeConstantRing U A) (exchangeConstantIso f A)
    obtain ⟨ff⟩ := DerivedScalarMate.unaryWhiskering (PR.ι ⋙ DerivedCategory.Q) ff₂
    apply ff.map_injective
    apply NatTrans.ext
    funext X
    obtain ⟨P, hP⟩ := X
    obtain ⟨hr, hs⟩ := comparisonOnRepresentatives d f n a b P F hP hF rV hrV
    let p := δ.hom.app P
    let c := δ.app F
    have : IsIso (Prod.mkHom p c.hom) :=
      (CategoryTheory.isIso_prod_iff _ _).2 ⟨inferInstance, inferInstance⟩
    apply (cancel_mono (b.tensor.map (Prod.mkHom p c.hom))).1
    have hc : b.tensor.map (Prod.mkHom (𝟙 _) c.inv) ≫
        b.tensor.map (Prod.mkHom p c.hom) = b.tensor.map (Prod.mkHom p (𝟙 _)) := by
      rw [← b.tensor.map_comp]
      congr 1
      exact Prod.ext (Category.id_comp p) c.inv_hom_id
    have hn := eU₀.hom.naturality p
    change RU.map p ≫ eU₀.hom.app (DerivedCategory.Q.obj (L.obj P)) =
      eU₀.hom.app (DP.obj (DerivedCategory.Q.obj P)) ≫
        b.tensor.map (Prod.mkHom p (𝟙 _)) at hn
    dsimp only [lhs, rhs, Functor.comp_map, NatTrans.comp_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app]
    change (DP.map (eV.hom.app _) ≫ μ.hom.app _) ≫ b.tensor.map _ =
      ((evaluatedPullIso d f n).hom.app _ ≫
        (eU₀.hom.app _ ≫ b.tensor.map (Prod.mkHom (𝟙 _) c.inv))) ≫ b.tensor.map _
    simp only [Category.assoc]
    erw [hc, ← hn]
    exact hs
  intro M
  have h := congr_app heq M
  simpa only [lhs, rhs, evaluatedPullIso, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, NatTrans.comp_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.map_id, NatTrans.id_app, Category.comp_id,
    Category.assoc, Category.id_comp] using h

end AlgebraicGeometry.Scheme.OrderedExchange
