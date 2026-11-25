/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedCoefficientCounit.RingedCoefficientCounitPresentations
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
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
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import WeilConjectures.CategoryTheory.RingedToposDerivedPushforwardComposition
import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutions
import WeilConjectures.Mathlib.Algebra.Homology.GrothendieckAbelian
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
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
import WeilConjectures.CategoryTheory.GeometricModuleConstruction
import WeilConjectures.CategoryTheory.RingedToposRingData
import WeilConjectures.CategoryTheory.AdjunctionRingOperations
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.CategoryTheory.GeometricModuleTransport
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.GeometricRingTransport
import Mathlib.CategoryTheory.Sites.Limits
import WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresRingCore
import WeilConjectures.CategoryTheory.SheafRingObjectReconstruction
import WeilConjectures.CategoryTheory.Adjunction.FiniteProductRingFunctor
import WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
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
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Sites.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import all WeilConjectures.Algebra.Homology.Ringed.RingedTopoiDerivedPullbackIndependentSupplement
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckCoefficientUniverse
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.ShrinkYoneda
import all WeilConjectures.CategoryTheory.RingedToposMorphism.RingedToposDerivedAdjunctionOfUniverses
import all WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
import all Mathlib.CategoryTheory.MorphismProperty.Comma
import all WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
import all Mathlib.CategoryTheory.Filtered.Basic
import all Mathlib.CategoryTheory.Limits.Cones
import all WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
import all Mathlib.CategoryTheory.Functor.Derived.Adjunction
import all Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import all WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge

set_option linter.privateModule false

/-!
# Existence of normalized derived coefficient presentations

Source: Stacks, Tags 07A6 and 0D6E.
(blueprint: lem-pur-ringed-coefficient-derived-presentation-exists).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v r w
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.RingedCoefficientCounit

-- A resolving-class left derived functor remains universal after postcomposition.
private theorem postLeftDerived
    {B E T : Type*} [Category B] [Category E] [Category T] [Abelian B] [Abelian E]
    [HasDerivedCategory.{w} B] [HasDerivedCategory.{w} E]
    (L : B ⥤ E) [L.Additive]
    (LF : DerivedCategory B ⥤ DerivedCategory E)
    (εh : DerivedCategory.Qh ⋙ LF ⟶
      L.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (hLF : LF.IsLeftDerivedFunctor εh (HomotopyCategory.quasiIso B (.up ℤ)))
    (P : Set (HomotopyCategory B (.up ℤ)))
    (hres : ∀ X, ∃ (Y : HomotopyCategory B (.up ℤ)) (s : Y ⟶ X),
      Y ∈ P ∧ HomotopyCategory.quasiIso B (.up ℤ) s)
    (hinv : ∀ X Y (s : X ⟶ Y), X ∈ P → Y ∈ P →
      HomotopyCategory.quasiIso B (.up ℤ) s →
      IsIso ((L.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh).map s))
    (ε : DerivedCategory.Q ⋙ LF ⟶ onComplex L ⋙ DerivedCategory.Q)
    (hεapp : ∀ K, ε.app K = εh.app ((HomotopyCategory.quotient B (.up ℤ)).obj K))
    (H : DerivedCategory E ⥤ T) :
    (LF ⋙ H).IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫ Functor.whiskerRight ε H)
      (HomologicalComplex.quasiIso B (.up ℤ)) := by
  let := hLF
  let := CategoryTheory.quasiIso_twoOutOfThree B
  have hc : ∀ X, ∃ Y, IsEssentiallyConstantProDiagram
      (MorphismProperty.Over.forget (HomotopyCategory.quasiIso B (.up ℤ)) ⊤ X ⋙
        Over.forget X ⋙ L.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) Y := by
    intro X
    obtain ⟨Y, _, hy, _⟩ := Functor.resolvingClass_essentialConstancy
      (HomotopyCategory.quasiIso B (.up ℤ))
      (L.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) P hres hinv X
    exact ⟨Y, hy⟩
  have : H.PreservesRightKanExtension
      (L.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) DerivedCategory.Qh :=
    _root_.pro_absolute (HomotopyCategory.quasiIso B (.up ℤ)) DerivedCategory.Qh
      (L.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) H hc
  have := Functor.IsLeftDerivedFunctor.isRightKanExtension LF εh
    (HomotopyCategory.quasiIso B (.up ℤ))
  have hLHh : (LF ⋙ H).IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫ Functor.whiskerRight εh H)
      (HomotopyCategory.quasiIso B (.up ℤ)) := ⟨inferInstance⟩
  let := hLHh
  obtain ⟨δ, hδ, hδapp⟩ := CategoryTheory.leftDerivedOnComplexes L H (LF ⋙ H)
    ((Functor.associator _ _ _).inv ≫ Functor.whiskerRight εh H)
  have hδeq : δ = (Functor.associator _ _ _).inv ≫ Functor.whiskerRight ε H := by
    apply NatTrans.ext
    funext X
    simp only [hδapp, NatTrans.comp_app, Functor.associator_inv_app,
      Functor.whiskerRight_app, Category.id_comp, hεapp]
  rw [hδeq] at hδ
  exact hδ

-- Descend the ordinary adjunction and retain its chain-map Hom normalization.
private theorem normalizedAdjunction
    (T : Type*) [Category T]
    {B E : Type*} [Category B] [Category E] [Abelian B] [Abelian E]
    [HasDerivedCategory.{w} B] [HasDerivedCategory.{w} E]
    [Abelian.HasKInjectiveResolutions E]
    (L : B ⥤ E) [L.Additive] (R : E ⥤ B) [R.Additive] (adj : L ⊣ R)
    (LF : DerivedCategory B ⥤ DerivedCategory E)
    (εh : DerivedCategory.Qh ⋙ LF ⟶
      L.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (hLF : LF.IsLeftDerivedFunctor εh (HomotopyCategory.quasiIso B (.up ℤ)))
    (P : Set (HomotopyCategory B (.up ℤ)))
    (hres : ∀ X, ∃ (Y : HomotopyCategory B (.up ℤ)) (s : Y ⟶ X),
      Y ∈ P ∧ HomotopyCategory.quasiIso B (.up ℤ) s)
    (hinv : ∀ X Y (s : X ⟶ Y), X ∈ P → Y ∈ P →
      HomotopyCategory.quasiIso B (.up ℤ) s →
      IsIso ((L.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh).map s)) :
    ∃ d : DerivedAdjunction L R adj, (∀ K,
      IsIso (εh.app ((HomotopyCategory.quotient B (.up ℤ)).obj K)) →
        IsIso (d.epsilon.app K)) ∧
      ∀ H : DerivedCategory E ⥤ T, (d.left ⋙ H).IsLeftDerivedFunctor
        ((Functor.associator _ _ _).inv ≫ Functor.whiskerRight d.epsilon H)
        (HomologicalComplex.quasiIso B (.up ℤ)) := by
  classical
  let := hLF
  obtain ⟨RF, η, hRF, hη⟩ := CategoryTheory.exists_derived R
  let := hRF
  obtain ⟨ε₀, hε₀, hεapp₀⟩ := CategoryTheory.leftDerivedOnComplexes L (𝟭 _) LF εh
  let ε : DerivedCategory.Q ⋙ LF ⟶ onComplex L ⋙ DerivedCategory.Q := ε₀
  have hε : LF.IsLeftDerivedFunctor ε (HomologicalComplex.quasiIso B (.up ℤ)) := hε₀
  have hεapp (K) : ε.app K = εh.app ((HomotopyCategory.quotient B (.up ℤ)).obj K) :=
    hεapp₀ K
  let := hε
  have hRFL : (RF ⋙ LF).IsRightDerivedFunctor
      (Functor.whiskerRight η LF ≫ (Functor.associator _ _ _).hom)
      (HomologicalComplex.quasiIso E (.up ℤ)) := by
    have hd : (CochainComplex.KInjectives.localizerMorphism E).Derives
        (onComplex R ⋙ DerivedCategory.Q ⋙ LF) := by
      intro I I' g hg
      have : IsIso (DerivedCategory.Q.map ((onComplex R).map g.hom)) :=
        (CategoryTheory.derives R) g hg
      exact LF.map_isIso (DerivedCategory.Q.map ((onComplex R).map g.hom))
    apply hd.isRightDerivedFunctor_of_isIso
    intro I
    have : IsIso (η.app I.obj) := hη I.obj I.property
    change IsIso (LF.map (η.app I.obj) ≫ 𝟙 _)
    infer_instance
  let := hRFL
  have hδ := postLeftDerived L LF εh hLF P hres hinv ε hεapp RF
  let := hδ
  let ac := adj.mapHomologicalComplex (.up ℤ)
  let d := ac.derived (HomologicalComplex.quasiIso B (.up ℤ))
    (HomologicalComplex.quasiIso E (.up ℤ)) ε η
  refine ⟨{
    left := LF
    right := RF
    epsilon := ε
    eta := η
    isLeft := hε
    isRight := hRF
    onInjective := hη
    adj := d
    homFormula := ?_
  }, ?_, ?_⟩
  · intro K I _ h
    change LF.map (DerivedCategory.Q.map h ≫ η.app I) ≫
      d.counit.app (DerivedCategory.Q.obj I) = _
    rw [Functor.map_comp, Category.assoc]
    have hd := ac.derivedε_fac_app (HomologicalComplex.quasiIso E (.up ℤ)) ε η I
    change LF.map (η.app I) ≫ d.counit.app (DerivedCategory.Q.obj I) = _ at hd
    rw [hd, ← Category.assoc]
    have hn := ε.naturality h
    dsimp only [Functor.comp_map] at hn
    rw [hn]
    simp only [Category.assoc, ← Functor.map_comp]
    rfl
  · intro K hK
    change IsIso (ε.app K)
    rw [hεapp]
    exact hK
  · intro H
    exact postLeftDerived L LF εh hLF P hres hinv ε hεapp H

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  [UnivLE.{max u v, r}] [EssentiallySmall.{r} C] [EssentiallySmall.{r} D]
  {JX : GrothendieckTopology C} {JY : GrothendieckTopology D}
  [JX.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [JY.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [JX.HasSheafCompose (forget AddCommGrpCat.{r})]
  [JY.HasSheafCompose (forget AddCommGrpCat.{r})]
  [HasSheafify JX AddCommGrpCat.{r}] [JX.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasSheafify JY AddCommGrpCat.{r}] [JY.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasWeakSheafify JX CommRingCat.{r}] [HasWeakSheafify JY CommRingCat.{r}]
  (A : CommRingCat.{r}) (RX RI : Sheaf JX CommRingCat.{r})
  (RY : Sheaf JY CommRingCat.{r})
  (inverse : Sheaf JY (Type r) ⥤ Sheaf JX (Type r))
  (direct : Sheaf JX (Type r) ⥤ Sheaf JY (Type r)) (geom : inverse ⊣ direct)
  [leftExact : PreservesFiniteLimits inverse]
  (IA : SheafOfModules.AlgebraicInverseImage inverse
    (constantRing JY A) (constantRing JX A))
  (IR : SheafOfModules.AlgebraicInverseImage inverse RY RI) (c : RI ⟶ RX)

end CategoryTheory.RingedCoefficientCounit
