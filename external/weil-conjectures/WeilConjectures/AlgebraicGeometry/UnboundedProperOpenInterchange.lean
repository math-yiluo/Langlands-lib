/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.RingTheory.TensorProduct.DirectLimitFG
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
public import WeilConjectures.Algebra.Homology.ChangeOfRingsTensorAcyclic
public import WeilConjectures.Algebra.Homology.KFlatResolution
public import WeilConjectures.Algebra.Homology.KFlatTensorConeTwoOutOfThree
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.EtaleLowerShriekBaseChangeMap
public import WeilConjectures.AlgebraicGeometry.ExactUnboundedExchange
public import WeilConjectures.AlgebraicGeometry.ProperSupportSheafComposition
public import WeilConjectures.CategoryTheory.Adjunction.FiniteProductRingFunctor
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutions
public import WeilConjectures.CategoryTheory.SheafRingObjectReconstruction
public import WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresRingCore
public import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekBaseChange
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Comp
import WeilConjectures.AlgebraicGeometry.DerivedExchangeModuleTermwise
import WeilConjectures.AlgebraicGeometry.EtaleModuleSheavesGrothendieckAbelian
import WeilConjectures.AlgebraicGeometry.OpenExtendedInjectiveProperAcyclic
import WeilConjectures.AlgebraicGeometry.UnboundedProperOpenPasting
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
import WeilConjectures.CategoryTheory.DerivedExactCompositionComparison
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper

-- Internal comparison lemmas are shared through private imports.
set_option linter.privateModule false

/-!
# Unbounded proper/open interchange and its canonical normalizations

Source: Stacks Project, More on Étale Cohomology, Tags 0F7B (case (b)), 0F7C, 0F7D
and 0F7F (auxiliary; not a blueprint node).

The sheaf isomorphism is specified by equality of its two maps into the common direct
image. This is precisely equality of the proper-support subsheaves, and fixes the map.
The derived isomorphism is specified on every K-injective representative and every
K-injective resolution of its open extension. All composition equations include the
canonical composition isomorphisms. No boundedness of the input is imposed.
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

attribute [local instance 2000] Abelian.toPreadditive

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

private theorem exists_sheafComparison (A : Type (u + 1)) [CommRing A]
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] [IsProper r] [IsProper p]
    (sq : CommSq k r p i) :
    ∃ θ : (r)_*[ModuleCat.{u + 1} A] ⋙ (i)_!open[ModuleCat.{u + 1} A] ≅
        (k)_!open[ModuleCat.{u + 1} A] ⋙ (p)_*[ModuleCat.{u + 1} A],
      ∀ F, θ.hom.app F ≫
          (p)_*[ModuleCat.{u + 1} A].map
            ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) k).app F) ≫
          (lowerStarComp (ModuleCat.{u + 1} A) k p).hom.app F =
        (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) i).app
            ((r)_*[ModuleCat.{u + 1} A].obj F) ≫
          (lowerStarComp (ModuleCat.{u + 1} A) r i (k ≫ p) sq.w).hom.app F := by
  classical
  obtain ⟨L, ι, hι, hp, ho, c, e, hc, he, hce⟩ := properSupportSheafComposition A
  have hproper {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] : IsIso (ι f) := by
    have (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) : IsIso ((ι f).app F) :=
      hp X Y f F
    exact NatIso.isIso_of_isIso_app _
  have := hproper r
  have := hproper p
  obtain ⟨ok, hk⟩ := ho U V k
  obtain ⟨oi, hi⟩ := ho W Z i
  let er : L r ≅ (r)_*[ModuleCat.{u + 1} A] := asIso (ι r)
  let ep : L p ≅ (p)_*[ModuleCat.{u + 1} A] := asIso (ι p)
  have hcomp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
      [IsSeparated f] [LocallyOfFiniteType f] [IsSeparated g] [LocallyOfFiniteType g]
      (h : X ⟶ Z) [IsSeparated h] [LocallyOfFiniteType h] (hh : h = f ≫ g) :
      ∃ co : L f ⋙ L g ≅ L h, ∀ F,
        co.hom.app F ≫ (ι h).app F = (ι g).app ((L f).obj F) ≫
          (g)_*[ModuleCat.{u + 1} A].map ((ι f).app F) ≫
          (lowerStarComp (ModuleCat.{u + 1} A) f g h hh).hom.app F := by
    subst h
    exact ⟨c X Y Z f g, hc X Y Z f g⟩
  obtain ⟨co, hco⟩ := hcomp r i (k ≫ p) sq.w
  let t : (r)_*[ModuleCat.{u + 1} A] ⋙ (i)_!open[ModuleCat.{u + 1} A] ≅ L (k ≫ p) :=
    Functor.isoWhiskerRight er.symm _ ≪≫ Functor.isoWhiskerLeft _ oi ≪≫ co
  let b : (k)_!open[ModuleCat.{u + 1} A] ⋙ (p)_*[ModuleCat.{u + 1} A] ≅ L (k ≫ p) :=
    Functor.isoWhiskerLeft _ ep.symm ≪≫ Functor.isoWhiskerRight ok _ ≪≫ c U V Z k p
  refine ⟨t ≪≫ b.symm, fun F => ?_⟩
  have ht : t.hom.app F ≫ (ι (k ≫ p)).app F =
      (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) i).app
          ((r)_*[ModuleCat.{u + 1} A].obj F) ≫
        (lowerStarComp (ModuleCat.{u + 1} A) r i (k ≫ p) sq.w).hom.app F := by
    dsimp only [t, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Iso.symm_hom]
    simp only [Category.assoc]
    rw [hco]
    simp only [← Category.assoc, ← NatTrans.comp_app, hi]
    rw [(openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) i).naturality]
    simp only [Category.assoc]
    change _ ≫ (i)_*[ModuleCat.{u + 1} A].map (er.inv.app F) ≫
      (i)_*[ModuleCat.{u + 1} A].map (er.hom.app F) ≫ _ = _
    rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app,
      CategoryTheory.Functor.map_id, Category.id_comp]
  have hb : b.hom.app F ≫ (ι (k ≫ p)).app F =
      (p)_*[ModuleCat.{u + 1} A].map
          ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) k).app F) ≫
        (lowerStarComp (ModuleCat.{u + 1} A) k p).hom.app F := by
    dsimp only [b, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Iso.symm_hom]
    simp only [Category.assoc]
    rw [hc, reassoc_of% (ι p).naturality (ok.hom.app F)]
    change ep.inv.app _ ≫ ep.hom.app _ ≫ _ = _
    rw [Iso.inv_hom_id_app_assoc, ← Functor.map_comp_assoc, ← NatTrans.comp_app, hk]
  dsimp only [Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom]
  rw [← hb, Category.assoc, Iso.inv_hom_id_app_assoc]
  exact ht

private theorem exists_termwise_injective_resolution
    {C : Type v} [Category.{w} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
    (J : CochainComplex C ℤ) :
    ∃ J' : CochainComplex C ℤ, J'.IsKInjective ∧
      (∀ n, Injective (J'.X n)) ∧ ∃ a : J ⟶ J', QuasiIso a := by
  refine ⟨(CochainComplex.kInjectiveResolutionFunctor.{w} C).obj J,
    inferInstance, fun n => inferInstance,
    (CochainComplex.toKInjectiveResolution.{w} C).app J,
    (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{w} C J).2⟩

private theorem derivedUnit_of_termwise_injective_resolution
    {C₀ C₁ C₂ : Type v} [Category.{w} C₀] [Category.{w} C₁] [Category.{w} C₂]
    [Abelian C₀] [Abelian C₁] [Abelian C₂]
    [HasDerivedCategory C₀] [HasDerivedCategory C₁] [HasDerivedCategory C₂]
    [IsGrothendieckAbelian.{w} C₀] [IsGrothendieckAbelian.{w} C₁]
    [HasInjectiveResolutions C₁]
    [Abelian.HasKInjectiveResolutions C₀] [Abelian.HasKInjectiveResolutions C₁]
    (P : C₁ ⥤ C₂) (K : C₀ ⥤ C₁) [P.Additive] [K.Additive]
    [PreservesFiniteLimits P]
    (hacyclic : ∀ M : CochainComplex C₁ ℤ, M.Acyclic →
      (∀ n, P.rightAcyclic (M.X n)) → ((P.mapHomologicalComplex (.up ℤ)).obj M).Acyclic)
    (hterm : ∀ (F : C₀) [Injective F], P.rightAcyclic (K.obj F))
    (J : CochainComplex C₀ ℤ) [J.IsKInjective] :
    IsIso (P.rightDerivedFunctorUnit.app
      ((K.mapHomotopyCategory (.up ℤ)).obj ((HomotopyCategory.quotient _ _).obj J))) := by
  obtain ⟨J', hJ', hterms, a, hqa⟩ := exists_termwise_injective_resolution J
  have := hJ'
  have (n : ℤ) := hterms n
  have := hqa
  have ha : IsIso ((HomotopyCategory.quotient _ _).map a) := by
    have h := (CochainComplex.IsKInjective.quasiIso_iff a).mp inferInstance
    rwa [← HomotopyCategory.inverseImage_quotient_isomorphisms,
      MorphismProperty.inverseImage_iff, MorphismProperty.isomorphisms.iff] at h
  have hJ' : IsIso (P.rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient _ _).obj
        ((K.mapHomologicalComplex (.up ℤ)).obj J'))) :=
    P.isIso_rightDerivedFunctorUnit_app_of_rightAcyclic_of_map_acyclic
      hacyclic _ (fun n => hterm (J'.X n))
  exact (NatTrans.isIso_app_iff_of_iso P.rightDerivedFunctorUnit
    ((K.mapHomotopyCategory (.up ℤ)).mapIso
      (asIso ((HomotopyCategory.quotient _ _).map a)))).2 hJ'

private theorem openExtension_derivedUnit_isIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] [IsProper r] [IsProper p]
    (sq : CommSq k r p i)
    (J : CochainComplex (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    [J.IsKInjective] :
    IsIso (((p)_*[ModuleCat.{u + 1} A]).rightDerivedFunctorUnit.app
      (((k)_!open[ModuleCat.{u + 1} A].mapHomotopyCategory (.up ℤ)).obj
        ((HomotopyCategory.quotient _ _).obj J))) := by
  let P := (p)_*[ModuleCat.{u + 1} A]
  let K := (k)_!open[ModuleCat.{u + 1} A]
  have hacyclic (M : CochainComplex (Sheaf V.smallEtaleTopology
      (ModuleCat.{u + 1} A)) ℤ) (hM : M.Acyclic)
      (hM' : ∀ n, P.rightAcyclic (M.X n)) :
      ((P.mapHomologicalComplex (.up ℤ)).obj M).Acyclic := by
    choose d hd using exists_isZero_upperStar_rightDerived_lowerStar_of_isProper A
      (isAddTorsion_of_finite : IsAddTorsion A) p
    exact hM.map_of_rightAcyclic_of_forall_isZero P
      (fun z => (Z.algClosurePoint z)^*[ModuleCat.{u + 1} A])
      (isZero_of_forall_isZero_upperStar_algClosurePoint A) d hd hM'
  have hterm (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) [Injective F] :
      P.rightAcyclic (K.obj F) := by
    intro q
    exact (isZero_higherDirectImage_openImmersionLowerShriek_injective A
      k i r p sq.w F (q + 1) (by omega)).of_iso
        (P.homologyRightDerivedFunctorPlusObjSingleFunctorIso (K.obj F) (q + 1)).symm
  exact derivedUnit_of_termwise_injective_resolution
    (C₀ := Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A))
    (C₁ := Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A))
    (C₂ := Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)) P K hacyclic hterm J

private theorem comparison_representative
    {C₀ C₁ C₂ C₃ : Type v}
    [Category.{w} C₀] [Category.{w} C₁] [Category.{w} C₂] [Category.{w} C₃]
    [Abelian C₀] [Abelian C₁] [Abelian C₂] [Abelian C₃]
    [HasDerivedCategory C₀] [HasDerivedCategory C₁]
    [HasDerivedCategory C₂] [HasDerivedCategory C₃]
    [Abelian.HasKInjectiveResolutions C₀] [Abelian.HasKInjectiveResolutions C₁]
    (R : C₀ ⥤ C₂) (P : C₁ ⥤ C₃) (K : C₀ ⥤ C₁) (E : C₂ ⥤ C₃)
    [R.Additive] [P.Additive] [K.Additive] [E.Additive]
    [PreservesFiniteLimits K] [PreservesFiniteColimits K]
    [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    (θ : R ⋙ E ≅ K ⋙ P)
    (Γ : R.rightDerivedFunctor ⋙ E.mapDerivedCategory ≅
      K.mapDerivedCategory ⋙ P.rightDerivedFunctor)
    (J : CochainComplex C₀ ℤ) [J.IsKInjective]
    (I : CochainComplex C₁ ℤ) [I.IsKInjective]
    (ρ : (K.mapHomologicalComplex (.up ℤ)).obj J ⟶ I) [QuasiIso ρ]
    (h' :
      E.mapDerivedCategory.map (R.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ (.up
        ℤ)).obj J)) ≫
          Γ.hom.app (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj J)) =
        E.mapDerivedCategoryFactorsh.hom.app ((R.mapHomotopyCategory (.up ℤ)).obj
          ((HomotopyCategory.quotient _ (.up ℤ)).obj J)) ≫
          DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory θ.hom (.up ℤ)).app
            ((HomotopyCategory.quotient _ (.up ℤ)).obj J)) ≫
          P.rightDerivedFunctorUnit.app ((K.mapHomotopyCategory (.up ℤ)).obj
            ((HomotopyCategory.quotient _ (.up ℤ)).obj J)) ≫
          P.rightDerivedFunctor.map (K.mapDerivedCategoryFactorsh.inv.app
            ((HomotopyCategory.quotient _ (.up ℤ)).obj J))) :
        E.mapDerivedCategory.map
            ((R).rightDerivedFunctorObjQIso J).hom ≫
          (E).mapDerivedCategoryFactors.hom.app
            ((R.mapHomologicalComplex (.up ℤ)).obj J) ≫
          DerivedCategory.Q.map
            ((NatTrans.mapHomologicalComplex θ.hom (.up ℤ)).app J) ≫
          DerivedCategory.Q.map
            ((P.mapHomologicalComplex (.up ℤ)).map ρ) =
        Γ.hom.app (DerivedCategory.Q.obj J) ≫
          P.rightDerivedFunctor.map
            ((K).mapDerivedCategoryFactors.hom.app J ≫
              DerivedCategory.Q.map ρ) ≫
          ((P).rightDerivedFunctorObjQIso I).hom := by
  let qJ := (HomotopyCategory.quotient _ (.up ℤ)).obj J
  have hK : K.mapDerivedCategoryFactorsh.inv.app qJ ≫
      K.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso C₀).hom.app J) ≫
        K.mapDerivedCategoryFactors.hom.app J =
      (DerivedCategory.quotientCompQhIso C₁).hom.app
        ((K.mapHomologicalComplex (.up ℤ)).obj J) := by
    rw [← cancel_epi (K.mapDerivedCategoryFactorsh.hom.app qJ),
      Iso.hom_inv_id_app_assoc, K.mapDerivedCategoryFactorsh_hom_app]
    simp [Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift_inv]
  have hE : E.mapDerivedCategory.map
        ((DerivedCategory.quotientCompQhIso C₂).inv.app
          ((R.mapHomologicalComplex (.up ℤ)).obj J)) ≫
      E.mapDerivedCategoryFactorsh.hom.app ((R.mapHomotopyCategory (.up ℤ)).obj qJ) =
      E.mapDerivedCategoryFactors.hom.app ((R.mapHomologicalComplex (.up ℤ)).obj J) ≫
        (DerivedCategory.quotientCompQhIso C₃).inv.app
          ((E.mapHomologicalComplex (.up ℤ)).obj
            ((R.mapHomologicalComplex (.up ℤ)).obj J)) := by
    change E.mapDerivedCategory.map _ ≫ E.mapDerivedCategoryFactorsh.hom.app
      ((HomotopyCategory.quotient _ _).obj
        ((R.mapHomologicalComplex (.up ℤ)).obj J)) = _
    rw [E.mapDerivedCategoryFactorsh_hom_app]
    simp [Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift_inv,
      ← Functor.map_comp_assoc]
  have hn := Γ.hom.naturality ((DerivedCategory.quotientCompQhIso C₀).hom.app J)
  have ht := (DerivedCategory.quotientCompQhIso C₃).inv.naturality
    ((NatTrans.mapHomologicalComplex θ.hom (.up ℤ)).app J)
  have hu : E.mapDerivedCategory.map (R.rightDerivedFunctorUnitQ J) ≫
      Γ.hom.app (DerivedCategory.Q.obj J) ≫
        P.rightDerivedFunctor.map (K.mapDerivedCategoryFactors.hom.app J) =
      E.mapDerivedCategoryFactors.hom.app ((R.mapHomologicalComplex (.up ℤ)).obj J) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex θ.hom (.up ℤ)).app J) ≫
          P.rightDerivedFunctorUnitQ ((K.mapHomologicalComplex (.up ℤ)).obj J) := by
    simp only [Functor.comp_map] at hn ht
    simp only [Functor.rightDerivedFunctorUnitQ, Functor.map_comp, Category.assoc]
    rw [reassoc_of% hn, reassoc_of% h']
    simp only [← P.rightDerivedFunctor.map_comp]
    rw [hK]
    dsimp only [qJ] at hE
    rw [reassoc_of% hE]
    erw [← reassoc_of% ht]
    rfl
  rw [R.rightDerivedFunctorUnitQ_eq] at hu
  have hρ := P.rightDerivedFunctorUnitQ_naturality ρ
  rw [P.rightDerivedFunctorUnitQ_eq] at hρ
  rw [← cancel_epi (E.mapDerivedCategory.map (R.rightDerivedFunctorObjQIso J).inv),
    ← cancel_mono (P.rightDerivedFunctorObjQIso I).inv]
  simp only [← E.mapDerivedCategory.map_comp_assoc, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.id_comp, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]
  rw [hρ, ← reassoc_of% hu]
  simp only [Functor.map_comp]

private structure NormalizedDerivedComparison
    {C₀ C₁ C₂ C₃ : Type v}
    [Category.{w} C₀] [Category.{w} C₁] [Category.{w} C₂] [Category.{w} C₃]
    [Abelian C₀] [Abelian C₁] [Abelian C₂] [Abelian C₃]
    [HasDerivedCategory C₀] [HasDerivedCategory C₁]
    [HasDerivedCategory C₂] [HasDerivedCategory C₃]
    [Abelian.HasKInjectiveResolutions C₀] [Abelian.HasKInjectiveResolutions C₁]
    (R : C₀ ⥤ C₂) (P : C₁ ⥤ C₃) (K : C₀ ⥤ C₁) (E : C₂ ⥤ C₃)
    [R.Additive] [P.Additive] [K.Additive] [E.Additive]
    [PreservesFiniteLimits K] [PreservesFiniteColimits K]
    [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    (θ : R ⋙ E ≅ K ⋙ P) where
  comparison : R.rightDerivedFunctor ⋙ E.mapDerivedCategory ≅
        K.mapDerivedCategory ⋙ P.rightDerivedFunctor
  unit_normalization : (∀ X : HomotopyCategory C₀ (.up ℤ),
      E.mapDerivedCategory.map (R.rightDerivedFunctorUnit.app X) ≫
          comparison.hom.app (DerivedCategory.Qh.obj X) =
        E.mapDerivedCategoryFactorsh.hom.app ((R.mapHomotopyCategory (.up ℤ)).obj X) ≫
          DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory θ.hom (.up ℤ)).app X) ≫
          P.rightDerivedFunctorUnit.app ((K.mapHomotopyCategory (.up ℤ)).obj X) ≫
          P.rightDerivedFunctor.map (K.mapDerivedCategoryFactorsh.inv.app X))
  representative_normalization : ∀ (J : CochainComplex C₀ ℤ)
        [J.IsKInjective]
        (I : CochainComplex C₁ ℤ)
        [I.IsKInjective]
        (ρ : (K.mapHomologicalComplex (.up ℤ)).obj J ⟶ I)
        [QuasiIso ρ],
        E.mapDerivedCategory.map
            ((R).rightDerivedFunctorObjQIso J).hom ≫
          (E).mapDerivedCategoryFactors.hom.app
            ((R.mapHomologicalComplex (.up ℤ)).obj J) ≫
          DerivedCategory.Q.map
            ((NatTrans.mapHomologicalComplex θ.hom (.up ℤ)).app J) ≫
          DerivedCategory.Q.map
            ((P.mapHomologicalComplex (.up ℤ)).map ρ) =
        comparison.hom.app (DerivedCategory.Q.obj J) ≫
          P.rightDerivedFunctor.map
            ((K).mapDerivedCategoryFactors.hom.app J ≫
              DerivedCategory.Q.map ρ) ≫
          ((P).rightDerivedFunctorObjQIso I).hom

@[irreducible]
private noncomputable def constructedDerivedComparison
    {C₀ C₁ C₂ C₃ : Type v}
    [Category.{w} C₀] [Category.{w} C₁] [Category.{w} C₂] [Category.{w} C₃]
    [Abelian C₀] [Abelian C₁] [Abelian C₂] [Abelian C₃]
    [HasDerivedCategory C₀] [HasDerivedCategory C₁]
    [HasDerivedCategory C₂] [HasDerivedCategory C₃]
    [Abelian.HasKInjectiveResolutions C₀] [Abelian.HasKInjectiveResolutions C₁]
    (R : C₀ ⥤ C₂) (P : C₁ ⥤ C₃) (K : C₀ ⥤ C₁) (E : C₂ ⥤ C₃)
    [R.Additive] [P.Additive] [K.Additive] [E.Additive]
    [PreservesFiniteLimits K] [PreservesFiniteColimits K]
    [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    (hP : ∀ (J : CochainComplex C₀ ℤ) [J.IsKInjective],
      IsIso (P.rightDerivedFunctorUnit.app ((K.mapHomotopyCategory (.up ℤ)).obj
        ((HomotopyCategory.quotient _ _).obj J))))
    (θ : R ⋙ E ≅
      K ⋙ P) :
    NormalizedDerivedComparison R P K E θ := by
  let α := Functor.rightDerivedFunctorCompMapDerivedCategoryUnit R E
  let β := Functor.mapDerivedCategoryCompRightDerivedFunctorUnit K P
  have hβ : (K.mapDerivedCategory ⋙ P.rightDerivedFunctor).IsRightDerivedFunctor β
      (HomotopyCategory.quasiIso _ (.up ℤ)) := by
    refine (HomotopyCategory.KInjectives.localizerMorphism_derives
      ((K ⋙ P).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)).isRightDerivedFunctor_of_isIso
      β (fun X => ?_)
    obtain ⟨J, _, rfl⟩ := HomotopyCategory.KInjectives.mk_surjective X
    change IsIso (β.app ((HomotopyCategory.quotient _ _).obj J))
    have hPJ : IsIso (P.rightDerivedFunctorUnit.app
        ((K.mapHomotopyCategory (.up ℤ)).obj
          ((HomotopyCategory.quotient _ _).obj J))) :=
      hP J
    dsimp only [β]
    rw [Functor.mapDerivedCategoryCompRightDerivedFunctorUnit_app]
    infer_instance
  let θh : (R ⋙ E).mapHomotopyCategory (.up ℤ) ≅
      (K ⋙ P).mapHomotopyCategory (.up ℤ) :=
    { hom := NatTrans.mapHomotopyCategory θ.hom (.up ℤ)
      inv := NatTrans.mapHomotopyCategory θ.inv (.up ℤ)
      hom_inv_id := by rw [← NatTrans.mapHomotopyCategory_comp, θ.hom_inv_id,
        NatTrans.mapHomotopyCategory_id]
      inv_hom_id := by rw [← NatTrans.mapHomotopyCategory_comp, θ.inv_hom_id,
        NatTrans.mapHomotopyCategory_id] }
  let Γ := Functor.rightDerivedNatIso
    (R.rightDerivedFunctor ⋙ E.mapDerivedCategory)
    (K.mapDerivedCategory ⋙ P.rightDerivedFunctor) α β
    (HomotopyCategory.quasiIso _ (.up ℤ))
    (Functor.isoWhiskerRight θh DerivedCategory.Qh)
  have hn (X : HomotopyCategory C₀ (.up ℤ)) :
      E.mapDerivedCategory.map (R.rightDerivedFunctorUnit.app X) ≫
          Γ.hom.app (DerivedCategory.Qh.obj X) =
        E.mapDerivedCategoryFactorsh.hom.app ((R.mapHomotopyCategory (.up ℤ)).obj X) ≫
          DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory θ.hom (.up ℤ)).app X) ≫
          P.rightDerivedFunctorUnit.app ((K.mapHomotopyCategory (.up ℤ)).obj X) ≫
          P.rightDerivedFunctor.map (K.mapDerivedCategoryFactorsh.inv.app X) := by
    obtain ⟨J, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    have h := Functor.rightDerivedNatTrans_app
      (R.rightDerivedFunctor ⋙ E.mapDerivedCategory)
      (K.mapDerivedCategory ⋙ P.rightDerivedFunctor) α β
      (HomotopyCategory.quasiIso _ (.up ℤ))
      (Functor.whiskerRight (NatTrans.mapHomotopyCategory θ.hom (.up ℤ)) DerivedCategory.Qh)
      ((HomotopyCategory.quotient _ _).obj J)
    change α.app _ ≫ Γ.hom.app _ = _ at h
    let qJ := (HomotopyCategory.quotient _ (.up ℤ)).obj J
    have h' :
        E.mapDerivedCategory.map (R.rightDerivedFunctorUnit.app qJ) ≫
            Γ.hom.app (DerivedCategory.Qh.obj qJ) =
          E.mapDerivedCategoryFactorsh.hom.app ((R.mapHomotopyCategory (.up ℤ)).obj qJ) ≫
            DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory θ.hom (.up ℤ)).app qJ) ≫
            P.rightDerivedFunctorUnit.app ((K.mapHomotopyCategory (.up ℤ)).obj qJ) ≫
            P.rightDerivedFunctor.map (K.mapDerivedCategoryFactorsh.inv.app qJ) := by
      have hα := Functor.rightDerivedFunctorCompMapDerivedCategoryUnit_app' R E qJ
      have hβ : β.app qJ =
          P.rightDerivedFunctorUnit.app ((K.mapHomotopyCategory (.up ℤ)).obj qJ) ≫
            P.rightDerivedFunctor.map (K.mapDerivedCategoryFactorsh.inv.app qJ) := by
        have hc : (Functor.mapHomotopyCategoryCompIso
            (Iso.refl (K ⋙ P)) (.up ℤ)).inv.app qJ = 𝟙 _ := by
          change (HomotopyCategory.quotient _ _).map (𝟙 _) = 𝟙 _
          exact CategoryTheory.Functor.map_id _ _
        dsimp only [β]
        rw [Functor.mapDerivedCategoryCompRightDerivedFunctorUnit_app K P,
          hc, CategoryTheory.Functor.map_id, Category.id_comp]
      change α.app qJ ≫ Γ.hom.app (DerivedCategory.Qh.obj qJ) =
        DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory θ.hom (.up ℤ)).app qJ) ≫
          β.app qJ at h
      conv_rhs at h => rw [hβ]
      calc
        _ = E.mapDerivedCategoryFactorsh.hom.app
            ((R.mapHomotopyCategory (.up ℤ)).obj qJ) ≫
            α.app qJ ≫ Γ.hom.app (DerivedCategory.Qh.obj qJ) := by
          symm
          rw [hα]
          simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
        _ = _ := by
          simpa only [Category.assoc] using
            congrArg (fun f => E.mapDerivedCategoryFactorsh.hom.app
              ((R.mapHomotopyCategory (.up ℤ)).obj qJ) ≫ f) h
    exact h'
  refine ⟨Γ, hn, fun J _ I _ ρ _ => ?_⟩
  exact comparison_representative R P K E θ Γ J I ρ (hn _)

end AlgebraicGeometry.Etale
