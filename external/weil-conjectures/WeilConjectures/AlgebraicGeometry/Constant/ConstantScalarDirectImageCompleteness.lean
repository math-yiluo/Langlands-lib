/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Supporting.ConstantCompletionEquivalence
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import WeilConjectures.CategoryTheory.RingedSiteCompleteElement
public import WeilConjectures.CategoryTheory.RingedSiteLocalization
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import WeilConjectures.CategoryTheory.RingedSiteDerivedRestriction
public import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.AlgebraicGeometry.Constant.ConstantInverseImageSectionSupplement
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
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
import all WeilConjectures.AlgebraicGeometry.RestrictionSectionCompleteness
import all WeilConjectures.CategoryTheory.RingedSiteCompleteElement
import all WeilConjectures.CategoryTheory.RingedSiteLocalization
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import all Mathlib.CategoryTheory.Functor.OfSequence
import all Mathlib.CategoryTheory.Sites.LeftExact
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all WeilConjectures.CategoryTheory.RingedSiteDerivedRestriction
import all WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all WeilConjectures.Algebra.Homology.DerivedInternalHom
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import all WeilConjectures.AlgebraicGeometry.RestrictionDerivedProducts
import all WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all WeilConjectures.AlgebraicGeometry.RingedTopoiTensorSections
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import all WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement
import all WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import all WeilConjectures.CategoryTheory.DerivedCategory.AdjointFunctors
import all Mathlib.CategoryTheory.MorphismProperty.Comma
import all Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import all Mathlib.CategoryTheory.Functor.Derived.RightDerived
import all WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import all WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
import all Mathlib.CategoryTheory.Filtered.Basic
import all Mathlib.CategoryTheory.Limits.Cones
import all WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
import all Mathlib.Algebra.Homology.DerivedCategory.Fractions
import all WeilConjectures.CategoryTheory.DerivedCategory.EverywhereDefinedDerivedFunctors
import all Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import all Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import all WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge
import all WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
import all Mathlib.CategoryTheory.Functor.Derived.Adjunction
import all Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import all WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Homology.KFlatResolution
import all WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
import all WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
import all Mathlib.CategoryTheory.Adjunction.Additive
import all WeilConjectures.AlgebraicGeometry.LocalHomTowerCriterion
import all WeilConjectures.CategoryTheory.LocalCoefficientLocalization
import all WeilConjectures.Algebra.Category.ModuleCat.Presheaf.InternalHom
import all Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import all WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import all WeilConjectures.Algebra.Homology.LocalCoefficientTelescopeDual
import all WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
import all WeilConjectures.Algebra.Homology.HomComplexProjections
import all WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationIsIso
import all WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationComm
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHomFree
import all WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
import all Mathlib.Algebra.Homology.HomologicalComplexLimits
import all Mathlib.Algebra.Homology.DerivedCategory.KInjective
import all WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import all WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
import all WeilConjectures.CategoryTheory.Ringed.RingedInternalHomExactRestrictionSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHomCoproduct
import all WeilConjectures.CategoryTheory.SequentialTelescopeMono
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
import all Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import all Mathlib.Algebra.Category.ModuleCat.Abelian
import all Mathlib.Algebra.Homology.DerivedCategory.Linear
import all Mathlib.Algebra.Module.ULift
import all Mathlib.RingTheory.Localization.Away.Basic
import all WeilConjectures.RingTheory.ModuleLocalizationTowerVanishing
import all Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import all WeilConjectures.CategoryTheory.Triangulated.DerivedLimitExistence
import WeilConjectures.AlgebraicGeometry.Exact.ExactPullbackDerivedAdjunction
import WeilConjectures.AlgebraicGeometry.ConstantPullbackScalar
import WeilConjectures.SixFunctors.Supporting.ConstantCompletionEquivalence
import WeilConjectures.AlgebraicGeometry.Constant.ConstantInverseImageSectionSupplement
import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
import WeilConjectures.CategoryTheory.LocalizedModuleExactForSystems
import WeilConjectures.Algebra.Homology.SmoothPurity.LocalizedModuleExactIndependent
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-! # Direct image preserves local derived completeness -/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.ConstantCompletion

private def scalarModule
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u})
    (a : (R.obj ⋙ forget CommRingCat).sections) : 𝟭 (Mod R) ⟶ 𝟭 (Mod R) where
  app M := ⟨PresheafOfModules.sectionsSMul M.val a⟩
  naturality {_ _} f := by
    apply SheafOfModules.hom_ext
    exact PresheafOfModules.sectionsSMul_naturality f.val a

private def scalarComplex
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u})
    (a : (R.obj ⋙ forget CommRingCat).sections) :
    𝟭 (CochainComplex (Mod R) ℤ) ⟶ 𝟭 (CochainComplex (Mod R) ℤ) where
  app P :=
    { f := fun n ↦ (scalarModule R a).app (P.X n)
      comm' := fun i j _ ↦ ((scalarModule R a).naturality (P.d i j)).symm }
  naturality {_ _} f := by
    apply HomologicalComplex.hom_ext
    intro n
    exact (scalarModule R a).naturality (f.f n)

private def scalarDerived
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (Mod R)]
    (a : (R.obj ⋙ forget CommRingCat).sections) :
    𝟭 (DerivedCategory (Mod R)) ⟶ 𝟭 (DerivedCategory (Mod R)) :=
  letI : Localization.Lifting DerivedCategory.Q
      (HomologicalComplex.quasiIso (Mod R) (.up ℤ))
      (𝟭 (CochainComplex (Mod R) ℤ) ⋙ DerivedCategory.Q) (𝟭 _) :=
    ⟨DerivedCategory.Q.rightUnitor ≪≫ DerivedCategory.Q.leftUnitor.symm⟩
  Localization.liftNatTrans DerivedCategory.Q
    (HomologicalComplex.quasiIso (Mod R) (.up ℤ)) _ _ _ _
    (Functor.whiskerRight (scalarComplex R a)
      DerivedCategory.Q)

private theorem scalarDerived_fac
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (Mod R)]
    (a : (R.obj ⋙ forget CommRingCat).sections) (P : CochainComplex (Mod R) ℤ) :
    (scalarDerived R a).app (DerivedCategory.Q.obj P) =
      DerivedCategory.Q.map ((scalarComplex R a).app P) := by
  simp only [scalarDerived, Localization.liftNatTrans_app]
  dsimp only [Localization.Lifting.iso, Iso.trans_hom, Iso.trans_inv,
    Functor.rightUnitor_hom_app, Functor.leftUnitor_inv_app,
    Functor.rightUnitor_inv_app, Functor.leftUnitor_hom_app]
  simp

private def exact_adjunction
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    (F : A ⥤ B) (G : B ⥤ A) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (a : F ⊣ G) :
    F.mapDerivedCategory ⊣ G.mapDerivedCategory := by
  let : CatCommSq (F.mapHomologicalComplex (.up ℤ))
      DerivedCategory.Q DerivedCategory.Q F.mapDerivedCategory :=
    ⟨F.mapDerivedCategoryFactors.symm⟩
  let : CatCommSq (G.mapHomologicalComplex (.up ℤ))
      DerivedCategory.Q DerivedCategory.Q G.mapDerivedCategory :=
    ⟨G.mapDerivedCategoryFactors.symm⟩
  exact (a.mapHomologicalComplex (.up ℤ)).localization
    DerivedCategory.Q (HomologicalComplex.quasiIso A (.up ℤ))
    DerivedCategory.Q (HomologicalComplex.quasiIso B (.up ℤ)) _ _

private theorem slice_rightAdjoint
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) (U : C)
    [HasDerivedCategory.{w} (Mod R)]
    [HasDerivedCategory.{w} (SheafOfModules.{u} ((siteModuleRings R).over U))] :
    (localCoefficientDerivedRestriction R U).IsRightAdjoint := by
  exact (exact_adjunction _ _
    (SheafOfModules.localizedSystemAdjunction.{u, u, u} R U)).isRightAdjoint

private theorem slice_jointlyReflects
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) :
    JointlyReflectIsomorphisms
      (fun U : C ↦ SheafOfModules.overFunctor.{u} (siteModuleRings R) U) where
  isIso {M N} f hf := by
    have hi (U : Cᵒᵖ) : IsIso (f.val.app U) := by
      let E := SheafOfModules.forget ((siteModuleRings R).over U.unop) ⋙
        PresheafOfModules.evaluation _ (op (Over.mk (𝟙 U.unop)))
      exact E.map_isIso ((SheafOfModules.overFunctor.{u} (siteModuleRings R) U.unop).map f)
    let e : M.val ≅ N.val := PresheafOfModules.isoMk (fun U ↦ asIso (f.val.app U))
      (fun {_ _} g ↦ f.val.naturality g)
    have he : ((SheafOfModules.fullyFaithfulForget _).preimageIso e).hom = f := by
      apply (SheafOfModules.forget _).map_injective
      rfl
    rw [← he]
    infer_instance

private theorem scalar_restriction
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (Mod R)]
    [∀ U : C, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((siteModuleRings R).over U))]
    (a : (R.obj ⋙ forget CommRingCat).sections) (U : C) :
    Functor.whiskerRight (scalarDerived R a) (localCoefficientDerivedRestriction R U) =
      localSectionDerivedMultiplication R U (a.val (op U)) := by
  have := (localCoefficientRestriction_exact R U).1
  have := (localCoefficientRestriction_exact R U).2.1
  have := (localCoefficientRestriction_exact R U).2.2
  let T := SheafOfModules.overFunctor.{u} (siteModuleRings R) U
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso (Mod R) (.up ℤ))
  intro P
  apply (cancel_mono (T.mapDerivedCategoryFactors.hom.app P)).mp
  rw [multiplication_fac R U (a.val (op U)) P]
  change T.mapDerivedCategory.map ((scalarDerived R a).app (DerivedCategory.Q.obj P)) ≫
    T.mapDerivedCategoryFactors.hom.app P = _
  rw [scalarDerived_fac]
  have hn := T.mapDerivedCategoryFactors.hom.naturality ((scalarComplex R a).app P)
  dsimp only [Functor.comp_map, Functor.id_obj] at hn
  rw [hn]
  congr 1
  apply congrArg DerivedCategory.Q.map
  ext n V x
  change a.val (op V.unop.left) • x = R.obj.map V.unop.hom.op (a.val (op U)) • x
  have ha : R.obj.map V.unop.hom.op (a.val (op U)) = a.val (op V.unop.left) :=
    a.property V.unop.hom.op
  exact congrArg (fun b : R.obj.obj (op V.unop.left) ↦
    b • (show (P.X n).val.obj (op V.unop.left) from x)) ha.symm

private theorem tower_map_iso_iff
    {A B : Type*} [Category A] [Preadditive A] [Category B] [Preadditive B]
    (F : A ⥤ B) [F.Additive]
    (K : ℕ → A) [HasProduct K] [HasProduct (fun n ↦ F.obj (K n))]
    [PreservesLimit (Discrete.functor K) F] (f : ∀ n, K (n + 1) ⟶ K n) :
    IsIso (F.map (towerTransitionEndomorphism f)) ↔
      IsIso (towerTransitionEndomorphism (K := fun n ↦ F.obj (K n)) (fun n ↦ F.map (f n))) := by
  let e := PreservesProduct.iso F K
  have he : F.map (towerTransitionEndomorphism f) ≫ e.hom =
      e.hom ≫ towerTransitionEndomorphism (K := fun n ↦ F.obj (K n)) (fun n ↦ F.map (f n)) := by
    apply Pi.hom_ext
    intro n
    dsimp only [e]
    simp only [Category.assoc, PreservesProduct.iso_hom, piComparison_comp_π]
    rw [← F.map_comp,
      (towerTransitionEndomorphism_eq_iff f _).mp rfl n, F.map_sub, F.map_comp]
    simp [towerTransitionEndomorphism, towerProductShift]
  exact conjugate_isIso_iff e _ _ he

private theorem complete_iff_globalTower
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (R : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (Mod R)]
    [∀ U : C, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((siteModuleRings R).over U))]
    (a : (R.obj ⋙ forget CommRingCat).sections)
    (N : DerivedCategory (Mod R))
    [HasCountableProducts (DerivedCategory (Mod R))] :
    (∀ U : C, IsRingedSiteCompleteElement J R N U (a.val (op U))) ↔
      IsIso (towerTransitionEndomorphism (K := fun _ : ℕ ↦ N)
        (fun _ ↦ (scalarDerived R a).app N)) := by
  have : ∀ U : C, (SheafOfModules.overFunctor.{u} (siteModuleRings R) U).Additive :=
    fun U ↦ (localCoefficientRestriction_exact R U).1
  have : ∀ U : C, PreservesFiniteLimits
      (SheafOfModules.overFunctor.{u} (siteModuleRings R) U) :=
    fun U ↦ (localCoefficientRestriction_exact R U).2.1
  have : ∀ U : C, PreservesFiniteColimits
      (SheafOfModules.overFunctor.{u} (siteModuleRings R) U) :=
    fun U ↦ (localCoefficientRestriction_exact R U).2.2
  have hcons := Functor.jointlyReflectIsomorphisms_mapDerivedCategory
    (slice_jointlyReflects R)
  have hlocal (U : C) : IsRingedSiteCompleteElement J R N U (a.val (op U)) ↔
      IsIso ((localCoefficientDerivedRestriction R U).map
        (towerTransitionEndomorphism (K := fun _ : ℕ ↦ N)
          (fun _ ↦ (scalarDerived R a).app N))) := by
    have : IsGrothendieckAbelian.{u}
        (SheafOfModules.{u} ((siteModuleRings R).over U)) :=
      SheafOfModules.isGrothendieckAbelian _
    have : HasCountableProducts (DerivedCategory
        (SheafOfModules.{u} ((siteModuleRings R).over U))) := derived_products
    have : (localCoefficientDerivedRestriction R U).IsRightAdjoint := slice_rightAdjoint R U
    have : (localCoefficientDerivedRestriction R U).Additive :=
      inferInstanceAs
        (SheafOfModules.overFunctor.{u} (siteModuleRings R) U).mapDerivedCategory.Additive
    rw [completeElement_iff_towerIso]
    have hs := NatTrans.congr_app (scalar_restriction R a U) N
    change (localCoefficientDerivedRestriction R U).map ((scalarDerived R a).app N) =
      (localSectionDerivedMultiplication R U (a.val (op U))).app N at hs
    rw [← hs]
    exact (tower_map_iso_iff (localCoefficientDerivedRestriction R U)
      (fun _ : ℕ ↦ N) (fun _ ↦ (scalarDerived R a).app N)).symm
  constructor
  · intro h
    have : ∀ U : C, IsIso
      ((SheafOfModules.overFunctor.{u} (siteModuleRings R) U).mapDerivedCategory.map
        (towerTransitionEndomorphism (K := fun _ : ℕ ↦ N)
          (fun _ ↦ (scalarDerived R a).app N))) := fun U ↦ (hlocal U).mp (h U)
    exact hcons.isIso _
  · intro h U
    exact (hlocal U).mpr (by have := h; infer_instance)

/-- Direct image preserves vanishing for a scalar transported by the coefficient map.

Source: Stacks Project, algebraization.tex, Tags 099J and 0997;
sites-cohomology.tex, Tag 0A07
(blueprint: lem-sp-constant-scalar-direct-image-completeness).

Proof: the local Hom tower criterion identifies each slice test with invertibility
of its Roos endomorphism. Exact slice restriction has an exact left adjoint, hence its
derived functor preserves products. The slice restrictions jointly reflect module
isomorphisms by evaluation at each slice terminal object, and their exact derived
functors jointly reflect isomorphisms by cohomology. Product comparisons therefore
identify all the local tests with invertibility of the single global scalar-tower
endomorphism. The exact pullback derived-adjunction theorem and uniqueness of total
right derived functors make RF a right adjoint, so RF preserves products. Ordinary
pullback carries a constant scalar to its transported global section. Transposing this
scalar square through the counit
shows that G does too. Naturality of the derived comparison on a K-injective
representative then proves the scalar square for RF. Apply RF to the invertible global
Roos endomorphism and conjugate by its product comparison. Apply the global/local
criterion again to obtain every target slice test. This allows zero scalars, the zero
ring and empty sites and uses no ideal or finite-generation hypothesis. -/
theorem constantScalarDirectImage_complete
    {C E : Type u} [SmallCategory C] [SmallCategory E]
    (JC : GrothendieckTopology C) (JD : GrothendieckTopology E)
    (A : Type u) [CommRing A]
    {L : Sheaf JC (Type u) ⥤ Sheaf JD (Type u)}
    (V : Sheaf JD (Type u) ⥤ Sheaf JC (Type u)) (adj : L ⊣ V)
    [PreservesFiniteLimits L] (F : InverseImageData L)
    (G : Mod (constant JD A) ⥤+ Mod (constant JC A))
    (aM : pull F (constantMap F A) ⊣ G.obj)
    [PreservesFiniteLimits (pull F (constantMap F A))]
    [PreservesFiniteColimits (pull F (constantMap F A))]
    (RF : D (constant JD A) ⥤ D (constant JC A))
    (ηG : G.obj.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ Q (constant JC A) ⟶
      Q (constant JD A) ⋙ RF)
    (hRF : RF.IsRightDerivedFunctor ηG
      (HomologicalComplex.quasiIso (Mod (constant JD A)) (ComplexShape.up ℤ)))
    (hηG : ∀ J : Cx (constant JD A), J.IsKInjective → IsIso (ηG.app J))
    (a : A) (N : D (constant JD A))
    (hN : ∀ U : E, @IsRingedSiteCompleteElement E _ JD (constant JD A)
      (HasDerivedCategory.standard _) (fun _ ↦ HasDerivedCategory.standard _) N U
      ((transportedConstantSection F A a).val (op U))) :
    ∀ U : C, @IsRingedSiteCompleteElement C _ JC (constant JC A)
      (HasDerivedCategory.standard _) (fun _ ↦ HasDerivedCategory.standard _) (RF.obj N) U
      ((constantSection (J := JC) a).val (op U)) := by
  let : HasDerivedCategory (Mod (constant JC A)) := HasDerivedCategory.standard _
  let : HasDerivedCategory (Mod (constant JD A)) := HasDerivedCategory.standard _
  let : ∀ U : C, HasDerivedCategory
      (SheafOfModules.{u} ((siteModuleRings (constant JC A)).over U)) :=
    fun _ ↦ HasDerivedCategory.standard _
  let : ∀ U : E, HasDerivedCategory
      (SheafOfModules.{u} ((siteModuleRings (constant JD A)).over U)) :=
    fun _ ↦ HasDerivedCategory.standard _
  have : IsGrothendieckAbelian.{u} (Mod (constant JC A)) :=
    SheafOfModules.isGrothendieckAbelian _
  have : IsGrothendieckAbelian.{u} (Mod (constant JD A)) :=
    SheafOfModules.isGrothendieckAbelian _
  have : HasCountableProducts (D (constant JC A)) := derived_products
  have : HasCountableProducts (D (constant JD A)) := derived_products
  have := hRF
  obtain ⟨RF', η', hRF', _, aD, _⟩ :=
    exactPullbackDerivedAdjunction V adj F (constantMap F A) G aM
  have := hRF'
  have : RF'.IsRightAdjoint := aD.isRightAdjoint
  have : RF.IsRightAdjoint := Functor.isRightAdjoint_of_iso
    (Functor.rightDerivedUnique RF' RF η' ηG
      (HomologicalComplex.quasiIso (Mod (constant JD A)) (.up ℤ)))
  have : RF.Additive := Functor.additive_of_preserves_binary_products RF
  let μC := scalarModule (constant JC A) (constantSection (J := JC) a)
  let μD := scalarModule (constant JD A) (transportedConstantSection F A a)
  have hpull (M : Mod (constant JC A)) :
      (pull F (constantMap F A)).map (μC.app M) =
        μD.app ((pull F (constantMap F A)).obj M) := constantPullback_scalar A F a M
  have hG (M : Mod (constant JD A)) : G.obj.map (μD.app M) = μC.app (G.obj.obj M) := by
    apply (aM.homEquiv (G.obj.obj M) M).symm.injective
    rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit, hpull]
    exact (aM.counit.naturality (μD.app M)).trans (μD.naturality (aM.counit.app M))
  have hcomm : RF.map ((scalarDerived (constant JD A)
      (transportedConstantSection F A a)).app N) =
        (scalarDerived (constant JC A) (constantSection (J := JC) a)).app (RF.obj N) := by
    let P := (Q (constant JD A)).objPreimage N
    obtain ⟨J, hJ, j, _, hj⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective P
    have : QuasiIso j := hj
    have : IsIso (ηG.app J) := hηG J hJ
    let e : (Q (constant JD A)).obj J ≅ N :=
      (asIso ((Q (constant JD A)).map j)).symm ≪≫
        (Q (constant JD A)).objObjPreimageIso N
    let e' : (Q (constant JC A)).obj
        ((G.obj.mapHomologicalComplex (.up ℤ)).obj J) ≅ RF.obj N :=
      asIso (ηG.app J) ≪≫ RF.mapIso e
    let zC := scalarDerived (constant JC A) (constantSection (J := JC) a)
    let zD := scalarDerived (constant JD A) (transportedConstantSection F A a)
    have hg : (G.obj.mapHomologicalComplex (.up ℤ)).map
        ((scalarComplex (constant JD A) (transportedConstantSection F A a)).app J) =
      (scalarComplex (constant JC A) (constantSection (J := JC) a)).app
        ((G.obj.mapHomologicalComplex (.up ℤ)).obj J) := by
      apply HomologicalComplex.hom_ext
      intro n
      exact hG (J.X n)
    have hη := ηG.naturality
      ((scalarComplex (constant JD A) (transportedConstantSection F A a)).app J)
    dsimp only [Functor.comp_map] at hη
    rw [hg, ← scalarDerived_fac, ← scalarDerived_fac] at hη
    dsimp only [Functor.id_obj] at hη
    have he := zD.naturality e.hom
    dsimp only [Functor.id_map] at he
    have he' := congrArg RF.map he
    simp only [Functor.map_comp] at he'
    apply (cancel_epi e'.hom).mp
    change e'.hom ≫ RF.map (zD.app N) = e'.hom ≫ zC.app (RF.obj N)
    have hn := zC.naturality e'.hom
    dsimp only [Functor.id_map] at hn
    rw [hn]
    dsimp only [e', Iso.trans_hom, asIso_hom, Functor.mapIso_hom]
    simp only [Category.assoc]
    rw [he', ← Category.assoc, ← hη, Category.assoc]
  apply (complete_iff_globalTower JC (constant JC A)
    (constantSection (J := JC) a) (RF.obj N)).mpr
  have hi := (complete_iff_globalTower JD (constant JD A)
    (transportedConstantSection F A a) N).mp hN
  have := hi
  have him : IsIso (RF.map (towerTransitionEndomorphism (K := fun _ : ℕ ↦ N)
      (fun _ ↦ (scalarDerived (constant JD A) (transportedConstantSection F A a)).app N))) :=
    inferInstance
  have ht := (tower_map_iso_iff RF (fun _ : ℕ ↦ N)
    (fun _ ↦ (scalarDerived (constant JD A) (transportedConstantSection F A a)).app N)).mp him
  simpa only [hcomm] using ht

end CategoryTheory.ConstantCompletion
