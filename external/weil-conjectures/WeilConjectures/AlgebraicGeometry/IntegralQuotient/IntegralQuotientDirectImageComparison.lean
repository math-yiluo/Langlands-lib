/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralQuotient.IntegralQuotientProjectionMap
public import WeilConjectures.AlgebraicGeometry.IntegralQuotient.IntegralQuotientCoefficients
public import WeilConjectures.AlgebraicGeometry.QuotientChange.InternalDerivedScalarComparisons
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMap
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.SingleFunctor
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Generator.Basic
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
import WeilConjectures.AlgebraicGeometry.IntegralQuotient.IntegralQuotientResolutionNormalization
import WeilConjectures.AlgebraicGeometry.InternalScalarPullbackNormalization
import WeilConjectures.AlgebraicGeometry.InternalScalarMateProjection
import WeilConjectures.AlgebraicGeometry.QuotientChange.NormalizedScalarRestrictionPush
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralResiduePullFlatModelMateNormalized
import WeilConjectures.AlgebraicGeometry.QuotientChange.InternalScalarMateTransitivity
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.DualizableShortExact
import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapDualizable

/-! # Integral quotient comparison for unbounded direct image

The mate is formed with the actual derived adjunctions. Quotient levels are indexed by
n + 1 and every tensor product is the ordinary, uncompleted derived tensor product.

## References

* Stacks Tags 093M, 06YY, 0D6D, 0D6E, 0G7E, 07A6 and 0944
-/

@[expose] public noncomputable section

set_option linter.unusedVariables false
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry.ProEtale.QuotientChange
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace CategoryTheory.Functor

private theorem square_single
    {A B B' C : Type*} [Category A] [Category B] [Category B'] [Category C]
    [Abelian A] [Abelian B] [Abelian B'] [Abelian C]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory B'] [HasDerivedCategory C]
    (R : A ⥤ B) (G : B ⥤ C) (L : A ⥤ B') (S : B' ⥤ C)
    [R.Additive] [G.Additive] [L.Additive] [S.Additive]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    (e : R ⋙ G ≅ L ⋙ S) (M : A) :
    (mapDerivedCategoryCompIso R G).hom.app
        ((DerivedCategory.singleFunctor A 0).obj M) ≫
      (mapDerivedCategoryNatIso e).hom.app _ ≫
      (mapDerivedCategoryCompIso L S).inv.app _ ≫
      S.mapDerivedCategory.map ((L.mapDerivedCategorySingleFunctor 0).hom.app M) ≫
      (S.mapDerivedCategorySingleFunctor 0).hom.app (L.obj M) =
    G.mapDerivedCategory.map ((R.mapDerivedCategorySingleFunctor 0).hom.app M) ≫
      (G.mapDerivedCategorySingleFunctor 0).hom.app (R.obj M) ≫
      (DerivedCategory.singleFunctor C 0).map (e.hom.app M) := by
  rw [mapDerivedCategoryCompIso_hom_app_singleFunctor,
    mapDerivedCategoryNatIso_hom_app_singleFunctor]
  rw [← mapDerivedCategoryCompIso_hom_app_singleFunctor R G M]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]

private theorem exact_computation
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (G : C ⥤ D) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (LG : DerivedCategory C ⥤ DerivedCategory D)
    (c : DerivedCategory.Qh ⋙ LG ⟶ G.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (e : LG ≅ G.mapDerivedCategory)
    (he : Functor.whiskerLeft DerivedCategory.Qh e.hom ≫
      G.mapDerivedCategoryFactorsh.hom = c) (P : CochainComplex C ℤ) :
    LG.map ((DerivedCategory.quotientCompQhIso C).inv.app P) ≫
        c.app ((HomotopyCategory.quotient _ _).obj P) ≫
        DerivedCategory.Qh.map ((G.mapHomotopyCategoryFactors (.up ℤ)).hom.app P) ≫
        (DerivedCategory.quotientCompQhIso D).hom.app
          ((G.mapHomologicalComplex (.up ℤ)).obj P) =
      e.hom.app (DerivedCategory.Q.obj P) ≫ G.mapDerivedCategoryFactors.hom.app P := by
  rw [← he]
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app,
    mapDerivedCategoryFactorsh_hom_app, Category.assoc]
  erw [e.hom.naturality_assoc]
  simp only [← G.mapDerivedCategory.map_comp_assoc, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]
  simp only [← Category.assoc, ← DerivedCategory.Qh.map_comp,
    Iso.inv_hom_id_app]
  erw [DerivedCategory.Qh.map_id]
  simp only [DerivedCategory.quotientCompQhIso,
    HomologicalComplexUpToQuasiIso.quotientCompQhIso,
    Quotient.lift.isLift_inv, Quotient.lift.isLift_hom]
  simp only [Category.assoc]
  erw [Category.id_comp, Category.id_comp, Category.comp_id]

private theorem exact_single
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (G : C ⥤ D) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (LG : DerivedCategory C ⥤ DerivedCategory D)
    (c : DerivedCategory.Qh ⋙ LG ⟶ G.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (e : LG ≅ G.mapDerivedCategory)
    (he : Functor.whiskerLeft DerivedCategory.Qh e.hom ≫
      G.mapDerivedCategoryFactorsh.hom = c) {M : C} {N : D} (φ : G.obj M ⟶ N) :
    c.app ((HomotopyCategory.quotient _ _).obj
        ((HomologicalComplex.single C (.up ℤ) 0).obj M)) ≫
      DerivedCategory.Qh.map
        ((G.mapHomotopyCategoryFactors (.up ℤ)).hom.app _ ≫
          (HomotopyCategory.quotient _ _).map
            ((HomologicalComplex.singleMapHomologicalComplex G (.up ℤ) 0).hom.app M ≫
              (HomologicalComplex.single D (.up ℤ) 0).map φ)) =
    e.hom.app ((DerivedCategory.singleFunctor C 0).obj M) ≫
      (G.mapDerivedCategorySingleFunctor 0).hom.app M ≫
      (DerivedCategory.singleFunctor D 0).map φ := by
  rw [mapDerivedCategorySingleFunctor_hom_app_eq]
  have h := exact_computation G LG c e he
    ((HomologicalComplex.single C (.up ℤ) 0).obj M)
  simp only [DerivedCategory.quotientCompQhIso,
    HomologicalComplexUpToQuasiIso.quotientCompQhIso,
    Quotient.lift.isLift_inv, Quotient.lift.isLift_hom] at h
  simp only [Functor.map_comp, Category.assoc]
  erw [LG.map_id, Category.id_comp, Category.comp_id] at h
  erw [← reassoc_of% h]
  rfl

private theorem square_single_transport
    {A B B' C : Type*} [Category A] [Category B] [Category B'] [Category C]
    [Abelian A] [Abelian B] [Abelian B'] [Abelian C]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory B'] [HasDerivedCategory C]
    (R : A ⥤ B) (G : B ⥤ C) (L : A ⥤ B') (S : B' ⥤ C)
    [R.Additive] [G.Additive] [L.Additive] [S.Additive]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    (e : L ⋙ S ≅ R ⋙ G)
    (LG : DerivedCategory B ⥤ DerivedCategory C)
    (LL : DerivedCategory A ⥤ DerivedCategory B')
    (eg : LG ≅ G.mapDerivedCategory) (el : LL ≅ L.mapDerivedCategory)
    (M : A) (N : B') (φ : L.obj M ⟶ N) :
    LG.map ((R.mapDerivedCategorySingleFunctor 0).inv.app M) ≫
      eg.hom.app (R.mapDerivedCategory.obj ((DerivedCategory.singleFunctor A 0).obj M)) ≫
      (mapDerivedCategoryCompIso R G).hom.app
        ((DerivedCategory.singleFunctor A 0).obj M) ≫
      (mapDerivedCategoryNatIso e).inv.app ((DerivedCategory.singleFunctor A 0).obj M) ≫
      (mapDerivedCategoryCompIso L S).inv.app ((DerivedCategory.singleFunctor A 0).obj M) ≫
      S.mapDerivedCategory.map (el.inv.app ((DerivedCategory.singleFunctor A 0).obj M)) ≫
      S.mapDerivedCategory.map (el.hom.app ((DerivedCategory.singleFunctor A 0).obj M)) ≫
      S.mapDerivedCategory.map ((L.mapDerivedCategorySingleFunctor 0).hom.app M) ≫
      S.mapDerivedCategory.map ((DerivedCategory.singleFunctor B' 0).map φ) ≫
      (S.mapDerivedCategorySingleFunctor 0).hom.app N =
    eg.hom.app ((DerivedCategory.singleFunctor B 0).obj (R.obj M)) ≫
      (G.mapDerivedCategorySingleFunctor 0).hom.app (R.obj M) ≫
      (DerivedCategory.singleFunctor C 0).map (e.inv.app M) ≫
      (DerivedCategory.singleFunctor C 0).map (S.map φ) := by
  rw [← S.mapDerivedCategory.map_comp_assoc, Iso.inv_hom_id_app,
    S.mapDerivedCategory.map_id, Category.id_comp]
  erw [eg.hom.naturality_assoc]
  have hn := (S.mapDerivedCategorySingleFunctor 0).hom.naturality φ
  dsimp only [Functor.comp_map] at hn
  rw [hn]
  have hs := square_single R G L S e.symm M
  simp only [mapDerivedCategoryNatIso_symm, Iso.symm_hom] at hs
  rw [reassoc_of% hs]
  rw [← G.mapDerivedCategory.map_comp_assoc, Iso.inv_hom_id_app,
    G.mapDerivedCategory.map_id, Category.id_comp]
  rfl

private theorem single_factor_map
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (G : C ⥤ D) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    {M : C} {N : D} (φ : G.obj M ⟶ N) :
    G.mapDerivedCategoryFactors.hom.app ((CochainComplex.singleFunctor C 0).obj M) ≫
      DerivedCategory.Q.map ((G.mapCochainComplexSingleFunctor 0).hom.app M ≫
        (CochainComplex.singleFunctor D 0).map φ) =
    (G.mapDerivedCategorySingleFunctor 0).hom.app M ≫
      (DerivedCategory.singleFunctor D 0).map φ := by
  rw [mapDerivedCategorySingleFunctor_hom_app_eq]
  simp only [Functor.map_comp, Category.assoc]
  rfl

private theorem exact_unit
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [MonoidalCategory C] [MonoidalPreadditive C]
    [∀ (X₁ X₂ : GradedObject ℤ C), X₁.HasTensor X₂]
    [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
    [DerivedCategory.Qh.HasDerivedMonoidalCategory (HomotopyCategory.quasiIso C (.up ℤ))]
    (G : C ⥤ D) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (LG : DerivedCategory C ⥤ DerivedCategory D)
    (c : DerivedCategory.Qh ⋙ LG ⟶ G.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (e : LG ≅ G.mapDerivedCategory)
    (he : Functor.whiskerLeft DerivedCategory.Qh e.hom ≫
      G.mapDerivedCategoryFactorsh.hom = c) {N : D} (φ : G.obj (𝟙_ C) ⟶ N) :
    c.app (𝟙_ (HomotopyCategory C (.up ℤ))) ≫
      DerivedCategory.Qh.map
        ((G.mapHomotopyCategoryFactors (.up ℤ)).hom.app (𝟙_ (CochainComplex C ℤ)) ≫
          (HomotopyCategory.quotient _ _).map
            ((HomologicalComplex.singleMapHomologicalComplex G (.up ℤ) 0).hom.app (𝟙_ C) ≫
              (HomologicalComplex.single D (.up ℤ) 0).map φ)) =
    e.hom.app (𝟙_ (DerivedCategory C)) ≫
      (G.mapDerivedCategorySingleFunctor 0).hom.app (𝟙_ C) ≫
      (DerivedCategory.singleFunctor D 0).map φ := by
  exact exact_single G LG c e he φ

end CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.QuotientChange

-- Keep the chosen section-category localization fixed across all proof applications.
@[instance_reducible]
private def proofSectionDerived
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (T : Scheme.{u}) :
    HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules Λ T) :=
  @HasDerivedCategory.ofIsGrothendieckAbelian _ _ _
    (SheafOfModules.isGrothendieckAbelianOfUniverses.{u + 1, u, u + 1, 0}
      (Scheme.ProEt.topology T) _)

attribute [local instance] proofSectionDerived

section ScalarNormalizations
variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']

private theorem tensorNormalization_exists
    (a : Λ ⟶ Λ') [IsMonHom a] (T : Scheme.{u}) :
    ∃ t : TensorNormalization a T, TensorNormalized a T t := by
  obtain ⟨t, _, _, _, _, ht, _⟩ := internal_scalar_pullback_normalization a (𝟙 T)
  exact ⟨t, ht⟩

private theorem pullNormalization_exists
    (a : Λ ⟶ Λ') [IsMonHom a]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃ b : D a Y ⋙ L Λ' f ≅ L Λ f ⋙ D a X, PullNormalized a f b := by
  obtain ⟨_, _, b, _, _, _, _, hb, _⟩ := internal_scalar_pullback_normalization a f
  exact ⟨b, hb⟩

private theorem normalizedProjectionEquation
    (a : Λ ⟶ Λ') [IsMonHom a] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (tX : TensorNormalization a X) (tY : TensorNormalization a Y)
    (b : D a Y ⋙ L Λ' f ≅ L Λ f ⋙ D a X)
    (hX : TensorNormalized a X tX) (hY : TensorNormalized a Y tY)
    (hb : PullNormalized a f b) (K : DerivedCategory (Modules Λ X)) :
    (V a Y).map ((rho a f b).app K) ≫
        (restrictPush a f b).hom.app ((D a X).obj K) ≫
        (F Λ f).map (tX.derived.hom.app K) =
      tY.derived.hom.app ((F Λ f).obj K) ≫ scalarProjection a f K := by
  rw [normalized_scalar_restriction_push a f b hb]
  exact (internal_scalar_mate_projection a f tX tY b hX hY hb).2.2.1 K

end ScalarNormalizations

private theorem scalarTower_of_comp_eq
    {Λ₀ Λ₁ Λ₂ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ₀] [IsCommMonObj Λ₀] [MonObj Λ₁] [IsCommMonObj Λ₁]
    [MonObj Λ₂] [IsCommMonObj Λ₂]
    (a : Λ₀ ⟶ Λ₁) [IsMonHom a] (d : Λ₁ ⟶ Λ₂) [IsMonHom d]
    (e : Λ₀ ⟶ Λ₂) [IsMonHom e] (he : a ≫ d = e)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (b01 : D a Y ⋙ L Λ₁ f ≅ L Λ₀ f ⋙ D a X)
    (b12 : D d Y ⋙ L Λ₂ f ≅ L Λ₁ f ⋙ D d X)
    (b02 : D e Y ⋙ L Λ₂ f ≅ L Λ₀ f ⋙ D e X)
    (h01 : PullNormalized a f b01) (h12 : PullNormalized d f b12)
    (h02 : PullNormalized e f b02) :
    ∃ (βX : D a X ⋙ D d X ≅ D e X) (βY : D a Y ⋙ D d Y ≅ D e Y),
      SuccessiveNormalized a d e he X βX ∧ SuccessiveNormalized a d e he Y βY ∧
      ∀ K : DerivedCategory (Modules Λ₀ X),
        βY.hom.app ((F Λ₀ f).obj K) ≫ (rho e f b02).app K =
          (D d Y).map ((rho a f b01).app K) ≫
            (rho d f b12).app ((D a X).obj K) ≫ (F Λ₂ f).map (βX.hom.app K) := by
  subst e
  obtain ⟨βX, βY, hX, hY, _, _, _, _, _, htower⟩ :=
    internal_scalar_mate_transitivity a d f b01 b12 b02 h01 h12 h02
  exact ⟨βX, βY, hX, hY, htower⟩

private theorem successiveNormalized_unique
    {Λ₀ Λ₁ Λ₂ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ₀] [IsCommMonObj Λ₀] [MonObj Λ₁] [IsCommMonObj Λ₁]
    [MonObj Λ₂] [IsCommMonObj Λ₂]
    (a : Λ₀ ⟶ Λ₁) [IsMonHom a] (b : Λ₁ ⟶ Λ₂) [IsMonHom b]
    (c : Λ₀ ⟶ Λ₂) [IsMonHom c] (h : a ≫ b = c) (T : Scheme.{u})
    (beta eta : D a T ⋙ D b T ≅ D c T)
    (hβ : SuccessiveNormalized a b c h T beta)
    (hγ : SuccessiveNormalized a b c h T eta) : beta = eta := by
  apply Iso.ext
  unfold SuccessiveNormalized at hβ hγ
  have hder : (D c T).IsLeftDerivedFunctor (scalarCounit c T)
      (HomotopyCategory.quasiIso (Modules Λ₀ T) (.up ℤ)) := by
    unfold D scalarCounit
    dsimp only [id]
    infer_instance
  apply Functor.leftDerived_ext _ (scalarCounit c T)
    (HomotopyCategory.quasiIso (Modules Λ₀ T) (.up ℤ)) _ beta.hom eta.hom
  ext P
  exact (hβ P).trans (hγ P).symm

end AlgebraicGeometry.ProEtale.QuotientChange

namespace AlgebraicGeometry.ProEtale.IntegralQuotient

attribute [local instance] proofSectionDerived

attribute [local irreducible] AlgebraicGeometry.ProEtale.upperStarFromPoint
  CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.rightDerivedFunctor CategoryTheory.Functor.mapDerivedCategory

set_option allowUnsafeReducibility true

attribute [local reducible] L F CondensedRing.moduleObjectDerivedPullback
  CondensedRing.moduleObjectDerivedPushforward
  CochainComplex.singleFunctors HomotopyCategory.singleFunctors DerivedCategory.singleFunctors

attribute [local instance] cachedProofInstance1 cachedProofInstance2 cachedProofInstance3
  cachedProofInstance4 cachedProofInstance5 cachedProofInstance7 cachedProofInstance8
  cachedProofInstance9 cachedProofInstance10 cachedProofInstance11 cachedProofInstance12

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

private theorem quotient_dualizable (T : Scheme.{u}) (n : ℕ) :
    IsDualizable (B (reduction l E n) T) := by
  obtain ⟨_, _, _, _, _, hn⟩ :=
    (integral_quotient_resolution_normalization l E).2.2 T
  obtain ⟨_, _, _, _, _, _, ε, _, hε, _⟩ := hn n
  have := hε
  have : (resolution l E T n).IsStrictlyGE (-1) := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    rw [resolution, CochainComplex.mappingCone.isZero_X_iff]
    exact ⟨HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega),
      HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)⟩
  have : (resolution l E T n).IsStrictlyLE 0 := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    rw [resolution, CochainComplex.mappingCone.isZero_X_iff]
    exact ⟨HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega),
      HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)⟩
  have hd : ∀ i : ℤ, IsDualizable ((resolution l E T n).X i) := by
    intro i
    exact DerivedCategory.isDualizable_mappingCone_single_X
      (X₁ := 𝟙_ (Modules (integral l E) T)) (X₂ := 𝟙_ (Modules (integral l E) T))
      ⟨inferInstance⟩ ⟨inferInstance⟩ _ i
  exact (DerivedCategory.isDualizable_Q_obj (resolution l E T n) (-1) 0 hd).of_iso
    (asIso (DerivedCategory.Q.map ε))

private theorem computePull_eq {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : CochainComplex (Modules Λ Y) ℤ) :
    computePull f P = (by
      unfold L CondensedRing.moduleObjectDerivedPullback
      exact (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ f).hom.app
          (DerivedCategory.Q.obj P) ≫
        (CondensedRing.upperStar Λ f).mapDerivedCategoryFactors.hom.app P) := by
  unfold computePull pullCounit L CondensedRing.moduleObjectDerivedPullback
    CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
  dsimp only [id]
  exact CategoryTheory.Functor.exact_computation _ _ _ _
    (CondensedRing.upperStar Λ f).leftDerivedFunctorIsoMapDerivedCategory_hom_fac P

attribute [-instance] ModuleRingedComparison.internalPullMonoidal in
private theorem pullUnit_eq
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (CondensedRing.leftDerivedUpperStarUnitIso Λ f).hom =
      (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ f).hom.app (𝟙_ _) ≫
        ((CondensedRing.upperStar Λ f).mapDerivedCategorySingleFunctor 0).hom.app
          (𝟙_ (Modules Λ Y)) ≫
        (DerivedCategory.singleFunctor (Modules Λ X) 0).map
          (Functor.Monoidal.εIso (CondensedRing.upperStar Λ f)).inv := by
  let φ : (CondensedRing.upperStar Λ f).obj (𝟙_ (Modules Λ Y)) ⟶
      𝟙_ (Modules Λ X) := (Functor.Monoidal.εIso (CondensedRing.upperStar Λ f)).inv
  have h := CategoryTheory.Functor.exact_unit
    (CondensedRing.upperStar Λ f) (CondensedRing.upperStar Λ f).leftDerivedFunctor
    (CondensedRing.upperStar Λ f).leftDerivedFunctorCounit
    (CondensedRing.upperStar Λ f).leftDerivedFunctorIsoMapDerivedCategory
    (CondensedRing.upperStar Λ f).leftDerivedFunctorIsoMapDerivedCategory_hom_fac φ
  unfold CondensedRing.leftDerivedUpperStarUnitIso
  dsimp only [Iso.trans_hom, Iso.app_hom, asIso_hom, Functor.mapIso_hom, Iso.symm_hom]
  convert h using 1
  dsimp only [CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory, id, φ]

attribute [-instance] ModuleRingedComparison.internalPullMonoidal in
private theorem scalarCoefficientPull_eq
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (scalarCoefficientPull a f).hom =
      computePull f ((CochainComplex.singleFunctor _ 0).obj (B₀ a Y)) ≫
        DerivedCategory.Q.map
          (((CondensedRing.upperStar Λ f).mapCochainComplexSingleFunctor 0).hom.app
              (B₀ a Y) ≫
            (CochainComplex.singleFunctor _ 0).map
              ((CondensedRing.comapUpperStarIso a f).inv.app
                (Mod.regular (condensedRingObj Λ' Y)) ≫
                (V₀ a X).map (Functor.Monoidal.εIso
                  (CondensedRing.upperStar Λ' f)).inv)) := by
  have hv (T : Scheme.{u}) : (scalarCoefficientUnit a T).hom =
      ((V₀ a T).mapDerivedCategorySingleFunctor 0).hom.app
        (Mod.regular (condensedRingObj Λ' T)) := by
    simpa only [scalarCoefficientUnit, cast_eq, Iso.trans_hom, Iso.app_hom,
      Functor.mapIso_hom, Functor.mapCochainComplexSingleFunctor, CochainComplex.singleFunctor,
      CochainComplex.singleFunctors] using
      ((V₀ a T).mapDerivedCategorySingleFunctor_hom_app_eq _).symm
  have hvi (T : Scheme.{u}) : (scalarCoefficientUnit a T).inv =
      ((V₀ a T).mapDerivedCategorySingleFunctor 0).inv.app
        (Mod.regular (condensedRingObj Λ' T)) := by
    apply (cancel_epi (scalarCoefficientUnit a T).hom).mp
    rw [Iso.hom_inv_id, hv, Iso.hom_inv_id_app]
    rfl
  have H := CategoryTheory.Functor.square_single_transport
    (V₀ a Y) (CondensedRing.upperStar Λ f) (CondensedRing.upperStar Λ' f) (V₀ a X)
    (CondensedRing.comapUpperStarIso a f) (CondensedRing.upperStar Λ f).leftDerivedFunctor
    (CondensedRing.upperStar Λ' f).leftDerivedFunctor
    (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ f)
    (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ' f)
    (Mod.regular (condensedRingObj Λ' Y))
    (Mod.regular (condensedRingObj Λ' X))
    (Functor.Monoidal.εIso (CondensedRing.upperStar Λ' f)).inv
  trans (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ f).hom.app
      (B a Y) ≫
    ((CondensedRing.upperStar Λ f).mapDerivedCategorySingleFunctor 0).hom.app (B₀ a Y) ≫
    (DerivedCategory.singleFunctor (Modules Λ X) 0).map
      ((CondensedRing.comapUpperStarIso a f).inv.app
        (Mod.regular (condensedRingObj Λ' Y)) ≫
        (V₀ a X).map (Functor.Monoidal.εIso (CondensedRing.upperStar Λ' f)).inv)
  · simp only [scalarCoefficientPull, scalarRestrictionPull, id, L,
      CondensedRing.moduleObjectDerivedPullback,
      Iso.trans_hom, Iso.trans_inv, Iso.app_hom, Iso.symm_hom,
      Iso.symm_inv, Functor.mapIso_hom, NatTrans.comp_app,
      Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, hv, hvi, pullUnit_eq,
      CondensedRing.derivedComapUpperStarIso,
      Functor.map_comp, Category.assoc]
    convert H using 1 <;> rfl
  · rw [computePull_eq]
    have h := CategoryTheory.Functor.single_factor_map (CondensedRing.upperStar Λ f)
      ((CondensedRing.comapUpperStarIso a f).inv.app
        (Mod.regular (condensedRingObj Λ' Y)) ≫
        (V₀ a X).map (Functor.Monoidal.εIso (CondensedRing.upperStar Λ' f)).inv)
    simpa only [id, Category.assoc] using congrArg
      (fun z ↦ (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ f).hom.app
        (B a Y) ≫ z) h.symm

private theorem coefficientPull_eq {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    (scalarCoefficientPull (reduction l E n) f).hom = coefficientPull l E f n := by
  exact scalarCoefficientPull_eq (reduction l E n) f

private theorem scalarProjection_eq {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (K : DerivedCategory (Modules (integral l E) X)) :
    scalarProjection (reduction l E n) f K = projectionMap l E f n K := by
  unfold scalarProjection projectionMap
  exact congrArg
    (fun z ↦ CondensedRing.moduleObjectProjectionMap (integral l E) f K
        (B (reduction l E n) Y) ≫
      (F (integral l E) f).map
        (((CondensedRing.derivedTensor (integral l E) X).obj K).map z))
    (coefficientPull_eq l E f n)

private theorem scalarProjection_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (K : DerivedCategory (Modules (integral l E) X)) :
    IsIso (scalarProjection (reduction l E n) f K) := by
  obtain ⟨br⟩ := DerivedCategory.nonempty_braidedCategory (Modules (integral l E) Y)
  let := br
  have hp := Adjunction.isIso_rightAdjointProjectionMap_app_app_of_isDualizable
    (CondensedRing.derivedUpperStarLowerStarAdjunction (integral l E) f)
    (CondensedRing.leftDerivedUpperStarTensor (integral l E) f)
    (fun _ _ ↦ rfl) K (quotient_dualizable l E Y n)
  unfold scalarProjection CondensedRing.moduleObjectProjectionMap
    CondensedRing.moduleObjectProjectionData
  dsimp only
  unfold F CondensedRing.moduleObjectDerivedPushforward
  apply IsIso.comp_isIso'
  · exact hp
  · have hi : IsIso
        ((((CondensedRing.derivedTensor (integral l E) X).obj K).map
          (scalarCoefficientPull (reduction l E n) f).hom)) :=
        Functor.map_isIso _ _
    exact Functor.map_isIso _ _

attribute [-instance] cachedProofInstance1 cachedProofInstance2 cachedProofInstance3
  cachedProofInstance4 cachedProofInstance5 cachedProofInstance7 cachedProofInstance8
  cachedProofInstance9 cachedProofInstance10 cachedProofInstance11 cachedProofInstance12 in
/-- The quotient-linear unbounded direct-image comparison, its exact projection
normalization, the actual augmented two-term resolution, and compatibility at all
positive quotient levels. No condition is imposed on the scheme morphism or complex. -/
theorem integral_quotient_direct_image_comparison :
    ∃ t : ∀ (T : Scheme.{u}) (n : ℕ), TensorNormalization (reduction l E n) T,
      (∀ (T : Scheme.{u}) (n : ℕ), TensorNormalized (reduction l E n) T (t T n)) ∧
      (∀ (T : Scheme.{u}) (n : ℕ),
        ∃ ε : resolution l E T n ⟶
            (CochainComplex.singleFunctor _ 0).obj (B₀ (reduction l E n) T),
          CochainComplex.mappingCone.inr
              ((CochainComplex.singleFunctor _ 0).map (multiplication l E T n)) ≫ ε =
            (CochainComplex.singleFunctor _ 0).map (projection l E T n) ∧
          QuasiIso ε ∧
          (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat (resolution l E T n) ∧
          (∀ i : ℤ, ObjectProperty.flat ((resolution l E T n).X i))) ∧
      ∃ b : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ),
          D (reduction l E n) Y ⋙ L (finite l E n) f ≅
            L (integral l E) f ⋙ D (reduction l E n) X,
        (∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ),
          PullNormalized (reduction l E n) f (b f n)) ∧
        (∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ),
          IsIso (rho (reduction l E n) f (b f n))) ∧
        (∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
            (K : DerivedCategory (Modules (integral l E) X)),
          (V (reduction l E n) Y).map ((rho (reduction l E n) f (b f n)).app K) ≫
              (restrictPush (reduction l E n) f (b f n)).hom.app
                ((D (reduction l E n) X).obj K) ≫
              (F (integral l E) f).map ((t X n).derived.hom.app K) =
            (t Y n).derived.hom.app ((F (integral l E) f).obj K) ≫
              projectionMap l E f n K) ∧
        (∀ (n m : ℕ) (h : m ≤ n),
          ∃ β : ∀ T : Scheme.{u},
              D (reduction l E n) T ⋙ D (finiteMap l E n m h) T ≅
                D (reduction l E m) T,
            (∀ T : Scheme.{u},
              SuccessiveNormalized (reduction l E n) (finiteMap l E n m h)
                (reduction l E m) (reduction_comp l E n m h) T (β T)) ∧
            ∃ c : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
                D (finiteMap l E n m h) Y ⋙ L (finite l E m) f ≅
                  L (finite l E n) f ⋙ D (finiteMap l E n m h) X,
              (∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
                PullNormalized (finiteMap l E n m h) f (c f)) ∧
              ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
                  (K : DerivedCategory (Modules (integral l E) X)),
                (β Y).hom.app ((F (integral l E) f).obj K) ≫
                    (rho (reduction l E m) f (b f m)).app K =
                  (D (finiteMap l E n m h) Y).map
                      ((rho (reduction l E n) f (b f n)).app K) ≫
                    (rho (finiteMap l E n m h) f (c f)).app
                      ((D (reduction l E n) X).obj K) ≫
                    (F (finite l E m) f).map ((β X).hom.app K)) := by
  classical
  have ht (T : Scheme.{u}) (n : ℕ) :
      ∃ t : TensorNormalization (reduction l E n) T,
        TensorNormalized (reduction l E n) T t := by
    exact tensorNormalization_exists (reduction l E n) T
  choose t ht using ht
  refine ⟨t, ht, ?_, ?_⟩
  · intro T n
    obtain ⟨α, c, hc, hα, hf, hn⟩ :=
      (integral_quotient_resolution_normalization l E).2.2 T
    obtain ⟨_, _, hflat, hk, _, _, ε, hε, hq, _⟩ := hn n
    refine ⟨ε, hε, hq, hk, ?_⟩
    intro i
    have h := hflat i
    have : PreservesFiniteLimits (tensorRight ((resolution l E T n).X i)) := h.1
    exact (ObjectProperty.flat_iff_preservesFiniteLimits _).2
      (preservesFiniteLimits_of_natIso
        (BraidedCategory.tensorLeftIsoTensorRight ((resolution l E T n).X i)).symm)
  · have hb {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
        ∃ b : D (reduction l E n) Y ⋙ L (finite l E n) f ≅
            L (integral l E) f ⋙ D (reduction l E n) X,
          PullNormalized (reduction l E n) f b := by
      exact pullNormalization_exists (reduction l E n) f
    choose b hb using @hb
    refine ⟨b, hb, ?_, ?_, ?_⟩
    · intro X Y f n
      have component (K : DerivedCategory (Modules (integral l E) X)) :
          IsIso ((rho (reduction l E n) f (b f n)).app K) := by
        have H := internal_scalar_mate_projection (reduction l E n) f
          (t X n) (t Y n) (b f n) (ht X n) (ht Y n) (hb f n)
        exact (H.2.2.2.2.1 K).mpr (scalarProjection_isIso l E f n K)
      exact NatIso.isIso_of_isIso_app _
    · intro X Y f n K
      have H := normalizedProjectionEquation (reduction l E n) f
        (t X n) (t Y n) (b f n) (ht X n) (ht Y n) (hb f n) K
      exact H.trans (congrArg
        (fun z ↦ (t Y n).derived.hom.app ((F (integral l E) f).obj K) ≫ z)
        (scalarProjection_eq l E f n K))
    · intro n m h
      let a := reduction l E n
      let d := finiteMap l E n m h
      let e := reduction l E m
      have he : a ≫ d = e := reduction_comp l E n m h
      have hc {X Y : Scheme.{u}} (f : X ⟶ Y) :
          ∃ c : D d Y ⋙ L (finite l E m) f ≅ L (finite l E n) f ⋙ D d X,
            PullNormalized d f c := by
        exact pullNormalization_exists d f
      choose c hc using @hc
      have tower {X Y : Scheme.{u}} (f : X ⟶ Y) :
          ∃ (βX : D a X ⋙ D d X ≅ D e X)
            (βY : D a Y ⋙ D d Y ≅ D e Y),
            SuccessiveNormalized a d e he X βX ∧
            SuccessiveNormalized a d e he Y βY ∧
            ∀ K : DerivedCategory (Modules (integral l E) X),
              βY.hom.app ((F (integral l E) f).obj K) ≫
                  (rho e f (b f m)).app K =
                (D d Y).map ((rho a f (b f n)).app K) ≫
                  (rho d f (c f)).app ((D a X).obj K) ≫
                  (F (finite l E m) f).map (βX.hom.app K) := by
        exact scalarTower_of_comp_eq a d e he f (b f n) (c f) (b f m)
          (hb f n) (hc f) (hb f m)
      have hβ (T : Scheme.{u}) :
          ∃ β : D a T ⋙ D d T ≅ D e T,
            SuccessiveNormalized a d e he T β := by
        obtain ⟨β, _, hβ, _⟩ := tower (𝟙 T)
        exact ⟨β, hβ⟩
      choose β hβ using hβ
      refine ⟨β, hβ, @c, @hc, ?_⟩
      intro X Y f K
      obtain ⟨βX, βY, hX, hY, htower⟩ := tower f
      have hX' := successiveNormalized_unique a d e he X βX (β X) hX (hβ X)
      have hY' := successiveNormalized_unique a d e he Y βY (β Y) hY (hβ Y)
      subst βX
      subst βY
      exact htower K

end AlgebraicGeometry.ProEtale.IntegralQuotient
