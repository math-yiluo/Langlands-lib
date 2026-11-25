/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Adjunction.Whiskering
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import WeilConjectures.CategoryTheory.RingedToposDerivedPushforwardComposition
import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutions
import WeilConjectures.Mathlib.Algebra.Homology.GrothendieckAbelian
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.CategoryTheory.RingedToposKFlatPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.CategoryTheory.GeometricModuleConstruction
import WeilConjectures.CategoryTheory.RingedToposRingData
import WeilConjectures.CategoryTheory.AdjunctionRingOperations
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.CategoryTheory.GeometricModuleTransport
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.GeometricRingTransport
import Mathlib.CategoryTheory.Sites.Limits
import WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresRingCore
import WeilConjectures.CategoryTheory.SheafRingObjectReconstruction
import WeilConjectures.CategoryTheory.Adjunction.FiniteProductRingFunctor
import WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.Additive
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import Mathlib.CategoryTheory.Types.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Limits.Types.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Sites.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective

/-!
# Normalized evaluation of a total derived tower functor

Source: Stacks Project, Sites Cohomology, Tag 0A07, lemma-Rf-commutes-with-Rlim,
diagram-topos proof, expanded using Derived Categories, Tags 070I, 070Y and 09T5
(blueprint: lem-weil-pbc-tower-derived-evaluation-normalization).

Natural number `n` denotes the positive tower level `n + 1`.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe uA vA uB vB wA wB wTA wTB uC vC wC

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Package Mathlib's pointwise limit-preservation instances for a termwise exact functor.
Source: Stacks Project, Tag 0A07, diagram-topos proof; Mathlib functor-category limits
(blueprint: lem-weil-pbc-tower-derived-evaluation-normalization). -/
instance towerNormalization_preservesFiniteLimits
    {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B]
    [HasFiniteLimits B] (F : B ⥤ A) [PreservesFiniteLimits F] :
    PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ B A).obj F) where
  preservesFiniteLimits _ _ _ := inferInstance

/-- Package Mathlib's pointwise colimit-preservation instances for a termwise exact functor.
Source: Stacks Project, Tag 0A07, diagram-topos proof; Mathlib functor-category colimits
(blueprint: lem-weil-pbc-tower-derived-evaluation-normalization). -/
instance towerNormalization_preservesFiniteColimits
    {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B]
    [HasFiniteColimits B] (F : B ⥤ A) [PreservesFiniteColimits F] :
    PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ B A).obj F) where
  preservesFiniteColimits _ _ _ := inferInstance

/-- The canonical transition between derived evaluations, obtained by localizing the
ordinary transition of exact evaluation functors. This includes every transition,
including the identity. Source: Stacks Project, Tag 0A07, diagram-topos proof;
Derived Categories, Tag 05RU
(blueprint: lem-weil-pbc-tower-derived-evaluation-normalization). -/
def towerDerivedEvaluationTransition
    (A : Type uA) [Category.{vA} A] [Abelian A]
    [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wTA} (ℕᵒᵖ ⥤ A)]
    {m n : ℕᵒᵖ} (t : m ⟶ n) :
    ((evaluation ℕᵒᵖ A).obj m).mapDerivedCategory ⟶
      ((evaluation ℕᵒᵖ A).obj n).mapDerivedCategory :=
  Localization.liftNatTrans DerivedCategory.Q
    (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (.up ℤ)) _ _
    ((evaluation ℕᵒᵖ A).obj m).mapDerivedCategory
    ((evaluation ℕᵒᵖ A).obj n).mapDerivedCategory
    (Functor.whiskerRight
      (NatTrans.mapHomologicalComplex ((evaluation ℕᵒᵖ A).map t) (.up ℤ))
      DerivedCategory.Q)

/-- The canonical exact-localization identification of evaluation after termwise `F`
with `F` after evaluation. It is the composite of the canonical composition comparisons;
its ordinary comparison is the strict evaluation identity. Source: Stacks Project,
Tag 0A07, diagram-topos proof, and Derived Categories, Tag 015F
(blueprint: lem-weil-pbc-tower-derived-evaluation-normalization). -/
def towerDerivedEvaluationInterchange
    {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B]
    [Abelian A] [Abelian B]
    [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
    [HasDerivedCategory.{wTA} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{wTB} (ℕᵒᵖ ⥤ B)]
    (F : B ⥤ A) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (n : ℕᵒᵖ) :
    ((Functor.whiskeringRight ℕᵒᵖ B A).obj F).mapDerivedCategory ⋙
        ((evaluation ℕᵒᵖ A).obj n).mapDerivedCategory ≅
      ((evaluation ℕᵒᵖ B).obj n).mapDerivedCategory ⋙ F.mapDerivedCategory :=
  Functor.mapDerivedCategoryCompIso
    ((Functor.whiskeringRight ℕᵒᵖ B A).obj F) ((evaluation ℕᵒᵖ A).obj n) ≪≫
    (Functor.mapDerivedCategoryCompIso ((evaluation ℕᵒᵖ B).obj n) F).symm

private theorem derivedComposition_fac
    {A : Type uA} {B : Type uB} {C : Type uC}
    [Category.{vA} A] [Category.{vB} B] [Category.{vC} C]
    [Abelian A] [Abelian B] [Abelian C]
    [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B] [HasDerivedCategory.{wC} C]
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (K : CochainComplex A ℤ) :
    (Functor.mapDerivedCategoryCompIso F G).inv.app (DerivedCategory.Q.obj K) ≫
        G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
        G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K) =
      (F ⋙ G).mapDerivedCategoryFactors.hom.app K := by
  have h := Functor.mapDerivedCategoryCompIso_fac F G K
  have hid : (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).hom.app K =
      𝟙 _ := rfl
  erw [hid, DerivedCategory.Q.map_id, Category.comp_id] at h
  exact h

private theorem towerInterchange_fac
    {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B]
    [Abelian A] [Abelian B]
    [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
    [HasDerivedCategory.{wTA} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{wTB} (ℕᵒᵖ ⥤ B)]
    (F : B ⥤ A) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (n : ℕᵒᵖ) (K : CochainComplex (ℕᵒᵖ ⥤ B) ℤ) :
    (towerDerivedEvaluationInterchange F n).hom.app (DerivedCategory.Q.obj K) ≫
        F.mapDerivedCategory.map
          (((evaluation ℕᵒᵖ B).obj n).mapDerivedCategoryFactors.hom.app K) ≫
        F.mapDerivedCategoryFactors.hom.app
          ((((evaluation ℕᵒᵖ B).obj n).mapHomologicalComplex (.up ℤ)).obj K) =
      ((evaluation ℕᵒᵖ A).obj n).mapDerivedCategory.map
          (((Functor.whiskeringRight ℕᵒᵖ B A).obj F).mapDerivedCategoryFactors.hom.app K) ≫
        ((evaluation ℕᵒᵖ A).obj n).mapDerivedCategoryFactors.hom.app
          ((((Functor.whiskeringRight ℕᵒᵖ B A).obj F).mapHomologicalComplex (.up ℤ)).obj K) := by
  let FT := (Functor.whiskeringRight ℕᵒᵖ B A).obj F
  let EA := (evaluation ℕᵒᵖ A).obj n
  let EB := (evaluation ℕᵒᵖ B).obj n
  apply (cancel_epi
    ((Functor.mapDerivedCategoryCompIso FT EA).inv.app (DerivedCategory.Q.obj K))).mp
  dsimp only [FT, EA, EB]
  simp only [towerDerivedEvaluationInterchange, Iso.trans_hom, NatTrans.comp_app,
    Iso.symm_hom, Category.assoc, Iso.inv_hom_id_app_assoc]
  exact (derivedComposition_fac EB F K).trans (derivedComposition_fac FT EA K).symm

private theorem towerTransition_fac
    (A : Type uA) [Category.{vA} A] [Abelian A]
    [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wTA} (ℕᵒᵖ ⥤ A)]
    {m n : ℕᵒᵖ} (t : m ⟶ n) (J : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    (towerDerivedEvaluationTransition A t).app (DerivedCategory.Q.obj J) ≫
        ((evaluation ℕᵒᵖ A).obj n).mapDerivedCategoryFactors.hom.app J =
      ((evaluation ℕᵒᵖ A).obj m).mapDerivedCategoryFactors.hom.app J ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex ((evaluation ℕᵒᵖ A).map t) (.up ℤ)).app J) := by
  have hm : Localization.Lifting.iso DerivedCategory.Q
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (.up ℤ))
      (((evaluation ℕᵒᵖ A).obj m).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
      ((evaluation ℕᵒᵖ A).obj m).mapDerivedCategory =
        ((evaluation ℕᵒᵖ A).obj m).mapDerivedCategoryFactors := rfl
  have hn : Localization.Lifting.iso DerivedCategory.Q
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (.up ℤ))
      (((evaluation ℕᵒᵖ A).obj n).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
      ((evaluation ℕᵒᵖ A).obj n).mapDerivedCategory =
        ((evaluation ℕᵒᵖ A).obj n).mapDerivedCategoryFactors := rfl
  simp [towerDerivedEvaluationTransition, Localization.liftNatTrans_app, hm, hn]

private theorem towerTransition_inv_fac
    (A : Type uA) [Category.{vA} A] [Abelian A]
    [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wTA} (ℕᵒᵖ ⥤ A)]
    {m n : ℕᵒᵖ} (t : m ⟶ n) (J : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    ((evaluation ℕᵒᵖ A).obj m).mapDerivedCategoryFactors.inv.app J ≫
        (towerDerivedEvaluationTransition A t).app (DerivedCategory.Q.obj J) =
      DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex ((evaluation ℕᵒᵖ A).map t) (.up ℤ)).app J) ≫
        ((evaluation ℕᵒᵖ A).obj n).mapDerivedCategoryFactors.inv.app J := by
  apply (cancel_mono
    (((evaluation ℕᵒᵖ A).obj n).mapDerivedCategoryFactors.hom.app J)).mp
  simp only [Category.assoc, towerTransition_fac, Iso.inv_hom_id_app_assoc,
    Iso.inv_hom_id_app]
  exact (Category.comp_id _).symm

private theorem exactDerivedAdjunction
    {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B]
    [Abelian A] [Abelian B]
    [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
    [Abelian.HasKInjectiveResolutions A]
    (F : B ⥤ A) (G : A ⥤ B) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (adj : F ⊣ G)
    (RG : DerivedCategory A ⥤ DerivedCategory B)
    (η : G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RG)
    [RG.IsRightDerivedFunctor η (HomologicalComplex.quasiIso A (.up ℤ))] :
    ∃ d : F.mapDerivedCategory ⊣ RG,
      ∀ (M : CochainComplex B ℤ) (I : CochainComplex A ℤ)
        (f : (F.mapHomologicalComplex (.up ℤ)).obj M ⟶ I),
        d.homEquiv (DerivedCategory.Q.obj M) (DerivedCategory.Q.obj I)
            (F.mapDerivedCategoryFactors.hom.app M ≫ DerivedCategory.Q.map f) =
          DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).homEquiv M I f) ≫
            η.app I := by
  let W := HomologicalComplex.quasiIso B (.up ℤ)
  let V := HomologicalComplex.quasiIso A (.up ℤ)
  let α := F.mapDerivedCategoryFactors.hom
  have : F.mapDerivedCategory.IsLeftDerivedFunctor α W :=
    Functor.isLeftDerivedFunctor_of_inverts W _ F.mapDerivedCategoryFactors
  have : (F.mapDerivedCategory ⋙ RG).IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫ Functor.whiskerRight α RG) W :=
    Functor.isLeftDerivedFunctor_of_inverts W _
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight F.mapDerivedCategoryFactors RG)
  have : (RG ⋙ F.mapDerivedCategory).IsRightDerivedFunctor
      (Functor.whiskerRight η F.mapDerivedCategory ≫
        (Functor.associator _ _ _).hom) V := by
    have hd : (CochainComplex.KInjectives.localizerMorphism A).Derives
        (G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⋙ F.mapDerivedCategory) := by
      intro I I' f hf
      have : IsIso (DerivedCategory.Q.map
          ((G.mapHomologicalComplex (.up ℤ)).map f.hom)) := (derives G) f hf
      exact F.mapDerivedCategory.map_isIso
        (DerivedCategory.Q.map ((G.mapHomologicalComplex (.up ℤ)).map f.hom))
    apply hd.isRightDerivedFunctor_of_isIso
    intro I
    have : IsIso (η.app I.obj) := (derives G).isIso_of_isRightDerivedFunctor η I
    change IsIso (F.mapDerivedCategory.map (η.app I.obj) ≫ 𝟙 _)
    infer_instance
  let ac := adj.mapHomologicalComplex (.up ℤ)
  let d := ac.derived W V α η
  refine ⟨d, ?_⟩
  intro M I f
  change d.unit.app _ ≫ RG.map (α.app M ≫ DerivedCategory.Q.map f) = _
  rw [RG.map_comp, ← Category.assoc]
  have hunit := ac.derivedη_fac_app W α η M
  change d.unit.app _ ≫ RG.map (α.app M) = _ at hunit
  have hn := η.naturality f
  dsimp only [Functor.comp_map] at hn
  rw [hunit, Category.assoc, ← hn, ← DerivedCategory.Q.map_comp_assoc]
  rfl

end CategoryTheory
