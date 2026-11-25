/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Brown.EtaleBrownProjectionRealization
public import WeilConjectures.AlgebraicGeometry.SystemProjection.EtaleSystemCoefficientProjection
public import WeilConjectures.Algebra.Homology.System.SystemLevelLeftExtension
public import WeilConjectures.Compactification.RefinementCategory
public import Mathlib.CategoryTheory.Shift.Adjunction
public import Mathlib.CategoryTheory.Triangulated.Adjunction
import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportConstruction
import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportScalarAction
import WeilConjectures.AlgebraicGeometry.Proper.ProperDerivedDirectImageCoproducts
import WeilConjectures.NumberTheory.Padics.NonunitCoefficientStages
import WeilConjectures.AlgebraicGeometry.Etale.Brown.EtaleBrownGeometricComparisons
import all WeilConjectures.Algebra.Homology.Coefficient.CoefficientEvaluationModels
import all WeilConjectures.Algebra.Homology.Coefficient.CoefficientSystemDerivedComparison
import all WeilConjectures.CategoryTheory.Exact.ExactDerivedAdjunctionBounds
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckCoefficientUniverse
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
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.ShrinkYoneda
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.Algebra.Homology.System.SystemGrothendieck
import WeilConjectures.Algebra.Homology.System.SystemCoproducts
import WeilConjectures.CategoryTheory.Exact.ExactFunctorCoproducts
import Mathlib.CategoryTheory.Functor.ReflectsIso.Limits
import WeilConjectures.CategoryTheory.GrothendieckDerivedBrownRightAdjoint
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
import WeilConjectures.CategoryTheory.GrothendieckDerivedBrownCohomologicalRepresentability
import Mathlib.CategoryTheory.Triangulated.Yoneda
import WeilConjectures.CategoryTheory.GrothendieckDerivedBrownRetract
import Mathlib.CategoryTheory.Retract
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import WeilConjectures.CategoryTheory.GrothendieckDerivedBrownRetractData
import Mathlib.CategoryTheory.Adjunction.Basic
import WeilConjectures.CategoryTheory.GrothendieckDerivedCompactLocalizationModel
import WeilConjectures.CategoryTheory.CompactlyGenerated
import Mathlib.CategoryTheory.Triangulated.Functor
import WeilConjectures.CategoryTheory.GrothendieckDerivedGabrielPopescuPresentation
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.CategoryTheory.Equivalence
import WeilConjectures.CategoryTheory.GabrielPopescuAbelianCore
import WeilConjectures.CategoryTheory.GabrielPopescuLargeHomRightAdjoint
import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import Mathlib.Algebra.Category.ModuleCat.Ulift
import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits
import WeilConjectures.CategoryTheory.DerivedLargeCoproductsTransfer
import WeilConjectures.CategoryTheory.DerivedHomologyInjective
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import WeilConjectures.CategoryTheory.DerivedHomologyInjectiveSurjective
import Mathlib.Algebra.Homology.SingleHomology
import WeilConjectures.CategoryTheory.DerivedHomologyInjectiveInjective
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import WeilConjectures.CategoryTheory.LargeHomSolutionSet
import Mathlib.CategoryTheory.Adjunction.AdjointFunctorTheorems
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.ModuleEmbedding.GabrielPopescu
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import WeilConjectures.CategoryTheory.CompactDerivedSourceCore
import WeilConjectures.CategoryTheory.DerivedModuleCompactGeneration
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.DerivedModuleRankOneProperties
import Mathlib.Algebra.Module.ULift
import WeilConjectures.CategoryTheory.CompactObject
import WeilConjectures.CategoryTheory.WeakTriangulatedGenerator
import WeilConjectures.CategoryTheory.DerivedModuleRankOneCompact
import WeilConjectures.CategoryTheory.DerivedModuleRankOneCompactInjective
import WeilConjectures.CategoryTheory.DerivedModuleRankOneCompactSurjective
import WeilConjectures.CategoryTheory.DerivedModuleDirectSums
import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Category.ModuleCat.Products
import WeilConjectures.CategoryTheory.DerivedModuleRankOneGenerator
import WeilConjectures.CategoryTheory.DerivedModuleRankOneNonzeroMap
import WeilConjectures.CategoryTheory.DerivedModuleNonzeroClassMap
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import WeilConjectures.CategoryTheory.TriangulatedEquivalenceTransfer
import WeilConjectures.CategoryTheory.CompactGenerationEquivalence
import Mathlib.CategoryTheory.Category.ULift
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.GrothendieckDerivedExactLocalization
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.FullyFaithful
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.CategoryTheory.BrownCohomologicalRepresentabilityUniverseTransfer
import Mathlib.CategoryTheory.Limits.Preserves.Opposites
import Mathlib.CategoryTheory.Triangulated.Opposite.Functor
import WeilConjectures.CategoryTheory.SmoothPurity.CountableCoproductsIdempotentComplete
import Mathlib.CategoryTheory.Adjunction.PartialAdjoint
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Brown adjunction on strict ordinary étale coefficient systems

Source: Zheng, Construction 4.1, Constructions 5.14--5.15, Lemma 5.16 and the
following Brown argument, printed pp. 21, 34--35
(blueprint: lem-pur-etale-system-brown-construction).

The positive level is `n+1`. The support presentation and scalar action are reused
from the existing ordinary étale interface. The record below contains conclusions,
including actual natural transformations in the derived category of strict systems.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite SheafOfModules
namespace AlgebraicGeometry

attribute [instance 5000] strictEtaleSystemDerived strictEtaleLevelDerived

variable (O : Type (u + 1)) [CommRing O] (t : O)
  {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)

/-- Componentwise coproducts, cohomology and bounds in the existing strict category.
This is a conclusion interface, imposing no normalization on its objects.
Source: Zheng, Construction 4.1 and Lemma 4.10, printed pp. 21, 23--24
(blueprint: lem-pur-etale-system-brown-construction). -/
structure StrictEtaleBrownComponents (W : Scheme.{u}) (P : StrictEtaleEvaluation W O t) where
  grothendieck : IsGrothendieckAbelian.{u + 1} (strictEtaleCoefficientSystem W O t)
  [coproducts : HasCoproducts.{u + 1} (strictEtaleCoefficientSystem W O t)]
  [derivedCoproducts : HasCoproducts.{u + 1}
    (DerivedCategory (strictEtaleCoefficientSystem W O t))]
  ordinary : ∀ (n : ℕ) (I : Type (u + 1)),
    PreservesColimitsOfShape (Discrete I)
      (coefficientEvaluation (J := W.smallEtaleTopology) (O := O) (ell := t) n)
  derived : ∀ (n : ℕ) (I : Type (u + 1)),
    PreservesColimitsOfShape (Discrete I) (P.evaluation n)
  cohomology : ∀ (n : ℕ) (q : ℤ),
    DerivedCategory.homologyFunctor (strictEtaleCoefficientSystem W O t) q ⋙
      coefficientEvaluation (J := W.smallEtaleTopology) (O := O) (ell := t) n ≅
    P.evaluation n ⋙ DerivedCategory.homologyFunctor (strictEtaleLevel W O t n) q
  bounds : ∀ (M : DerivedCategory (strictEtaleCoefficientSystem W O t)) (q : ℤ),
    (M.IsGE q ↔ ∀ n : ℕ, ((P.evaluation n).obj M).IsGE q) ∧
    (M.IsLE q ↔ ∀ n : ℕ, ((P.evaluation n).obj M).IsLE q)

/-- The Brown adjunction and the canonical left-extension comparison, with the
proper projection fixed by its geometric mate, and the open comparison by its mate.
Thus `projection` is the inverse of the coefficient projection `q`, rather than
an unspecified isomorphism having the same source and target.
Source: Zheng, Lemmas 5.13 and 5.16 and the following Brown argument, pp. 34--35
(blueprint: lem-pur-etale-system-brown-construction). -/
structure StrictEtaleBrownConstruction (S : StrictEtaleCompactSupport O t c) where
  componentsX : StrictEtaleBrownComponents O t X S.PX
  componentsZ : StrictEtaleBrownComponents O t c.Z S.PZ
  componentsY : StrictEtaleBrownComponents O t Y S.PY
  [additive : S.functor.Additive]
  [shift : S.functor.CommShift ℤ]
  [exact : S.functor.IsTriangulated]
  coproducts : ∀ I : Type (u + 1), PreservesColimitsOfShape (Discrete I) S.functor
  scalarX : StrictEtaleScalarAction X O t
  scalarY : StrictEtaleScalarAction Y O t
  linear : ∀ (r : O) (M : DerivedCategory (strictEtaleCoefficientSystem X O t)),
    S.functor.map ((scalarX.derived r).app M) =
      (scalarY.derived r).app (S.functor.obj M)
  right : DerivedCategory (strictEtaleCoefficientSystem Y O t) ⥤
    DerivedCategory (strictEtaleCoefficientSystem X O t)
  adjunction : S.functor ⊣ right
  [rightAdditive : right.Additive]
  [rightShift : right.CommShift ℤ]
  shiftAdjunction : adjunction.CommShift ℤ
  rightExact : right.IsTriangulated
  rightLinear : ∀ (r : O) (M : DerivedCategory (strictEtaleCoefficientSystem Y O t)),
    right.map ((scalarY.derived r).app M) = (scalarX.derived r).app (right.obj M)
  unitLinear : ∀ (r : O) (M : DerivedCategory (strictEtaleCoefficientSystem X O t)),
    adjunction.unit.app M ≫ (scalarX.derived r).app (right.obj (S.functor.obj M)) =
      (scalarX.derived r).app M ≫ adjunction.unit.app M
  counitLinear : ∀ (r : O) (M : DerivedCategory (strictEtaleCoefficientSystem Y O t)),
    (scalarY.derived r).app (S.functor.obj (right.obj M)) ≫ adjunction.counit.app M =
      adjunction.counit.app M ≫ (scalarY.derived r).app M
  realizationX : StrictEtaleBrownRealization O t X S.PX
  realizationZ : StrictEtaleBrownRealization O t c.Z S.PZ
  realizationY : StrictEtaleBrownRealization O t Y S.PY
  properRealization : ∀ n, StrictEtaleBrownImageRealization O t c.g n
    S.properImage (S.properDerived.level n) realizationZ realizationY
  openRealization : ∀ n, StrictEtaleBrownImageRealization O t c.i n
    S.openImage (S.openDerived.level n) realizationX realizationZ
  openComparison : ∀ n, S.levelDerivedOpen n ⋙ realizationZ.derived n ≅
    realizationX.derived n ⋙
      (Etale.openImmersionLowerShriek
        (ModuleCat.{u + 1} (strictEtaleBrownRing O t n)) c.i).mapDerivedCategory
  openComparison_mate : ∀ n,
    (mateEquiv (S.levelDerivedOpenAdjunction n)
      (((Etale.openImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} (strictEtaleBrownRing O t n))
        c.i).mapDerivedCategoryRightDerivedAdjunction).ofNatIsoRight
          (Etale.upperStar (ModuleCat.{u + 1} (strictEtaleBrownRing O t n))
            c.i).rightDerivedFunctorIsoMapDerivedCategory)
      (.mk _ _ _ _ (openComparison n).inv)) = (openRealization n).inverse.inv
  levelComparison : ∀ n, S.levelFunctor n ⋙ realizationY.derived n ≅
    realizationX.derived n ⋙ Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} (strictEtaleBrownRing O t n)) c
  levelComparison_def : ∀ n, levelComparison n =
    Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ (properRealization n).right ≪≫
      (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight (openComparison n) _ ≪≫
      Functor.associator _ _ _
  openProjection : ∀ {m n : ℕ} (h : m ≤ n),
    (S.PX.scalar h).derived ⋙ S.levelDerivedOpen m ≅
      S.levelDerivedOpen n ⋙ (S.PZ.scalar h).derived
  openMate : ∀ {m n : ℕ} (h : m ≤ n),
    (mateEquiv (S.levelDerivedOpenAdjunction n) (S.levelDerivedOpenAdjunction m)
      (.mk _ _ _ _ (openProjection h).hom)) = (S.openDerived.derivedTensor h).inv
  properProjection : ∀ {m n : ℕ} (h : m ≤ n),
    (S.PZ.scalar h).derived ⋙ (S.properDerived.level m).direct ≅
      (S.properDerived.level n).direct ⋙ (S.PY.scalar h).derived
  properMate : ∀ {m n : ℕ} (h : m ≤ n),
    (properProjection h).inv =
      (mateEquiv (S.properDerived.level n).adjunction (S.properDerived.level m).adjunction
        (.mk _ _ _ _ (S.properDerived.derivedTensor h).hom))
  projection : ∀ {m n : ℕ} (h : m ≤ n),
    (S.PX.scalar h).derived ⋙ S.levelFunctor m ≅
      S.levelFunctor n ⋙ (S.PY.scalar h).derived
  projection_def : ∀ {m n : ℕ} (h : m ≤ n),
    projection h = (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight (openProjection h) _ ≪≫ Functor.associator _ _ _ ≪≫
      isoWhiskerLeft _ (properProjection h) ≪≫ (Functor.associator _ _ _).symm
  projection_recorded_q : ∀ {m n : ℕ} (h : m ≤ n)
    (P : DerivedCategory (strictEtaleLevel X O t n)),
    (Etale.scalarExtension (strictEtaleBrownRingMap O t h) Y).map
        ((levelComparison n).inv.app P) ≫
      (realizationY.scalar h).inv.app ((S.levelFunctor n).obj P) ≫
      (realizationY.derived m).map ((projection h).inv.app P) ≫
      (levelComparison m).hom.app ((S.PX.scalar h).derived.obj P) ≫
      (Etale.rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} (strictEtaleBrownRing O t m)) c).map
          ((realizationX.scalar h).hom.app P) =
    (Etale.compactScalarMap (strictEtaleBrownRingMap O t h) c).app
      ((realizationX.derived n).obj P)
  properInsertion : ∀ n : ℕ,
    S.PY.derivedExtension n ⋙ S.properDerived.system.inverse ≅
      (S.properDerived.level n).inverse ⋙ S.PZ.derivedExtension n
  properInsertion_conjugate : ∀ n : ℕ,
    conjugateEquiv
      ((S.PY.derivedAdj n).comp S.properDerived.system.adjunction)
      (((S.properDerived.level n).adjunction).comp (S.PZ.derivedAdj n))
      (properInsertion n).inv = (S.properDerived.directEvaluation n).hom
  properInsertionMate : ∀ n : ℕ,
    (S.properDerived.level n).direct ⋙ S.PY.derivedExtension n ≅
      S.PZ.derivedExtension n ⋙ S.properDerived.system.direct
  properInsertionMate_def : ∀ n : ℕ,
    (properInsertionMate n).hom =
      (mateEquiv (S.properDerived.level n).adjunction S.properDerived.system.adjunction
        (.mk _ _ _ _ (properInsertion n).hom))
  openInsertion : ∀ n : ℕ,
    S.PX.derivedExtension n ⋙ S.derivedOpen ≅
      S.levelDerivedOpen n ⋙ S.PZ.derivedExtension n
  openInsertion_conjugate : ∀ n : ℕ,
    conjugateEquiv
      ((S.PX.derivedAdj n).comp S.derivedOpenAdjunction)
      ((S.levelDerivedOpenAdjunction n).comp (S.PZ.derivedAdj n))
      (openInsertion n).inv = (S.openDerived.inverseEvaluation n).hom
  leftExtension : ∀ n : ℕ,
    S.PX.derivedExtension n ⋙ S.functor ≅ S.levelFunctor n ⋙ S.PY.derivedExtension n
  leftExtension_def : ∀ n : ℕ,
    leftExtension n = (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight (openInsertion n) _ ≪≫ Functor.associator _ _ _ ≪≫
      isoWhiskerLeft _ (properInsertionMate n).symm ≪≫ (Functor.associator _ _ _).symm
  leftExtension_below : ∀ {m n : ℕ} (h : m ≤ n)
    (P : DerivedCategory (strictEtaleLevel X O t n)),
    (S.PY.evaluation m).map ((leftExtension n).hom.app P) ≫
      (S.PY.derivedBelow h).hom.app ((S.levelFunctor n).obj P) =
    (S.evaluation m).hom.app ((S.PX.derivedExtension n).obj P) ≫
      (S.levelFunctor m).map ((S.PX.derivedBelow h).hom.app P) ≫
        (projection h).hom.app P

universe a b w dA dB v u' v'
private theorem preserveViaEquivalences
    {A : Type a} {B : Type b} {C : Type u'} {D : Type v'}
    [Category.{v} A] [Category.{w} B] [Category.{dA} C] [Category.{dB} D]
    {J : Type u} [Category J]
    (F : A ⥤ B) (R : C ⥤ D) (U : A ⥤ C) (V : B ⥤ D)
    [U.IsEquivalence] [V.IsEquivalence] [PreservesColimitsOfShape J R]
    (e : F ⋙ V ≅ U ⋙ R) : PreservesColimitsOfShape J F := by
  have : PreservesColimitsOfShape J (U ⋙ R) := inferInstance
  have : PreservesColimitsOfShape J (F ⋙ V) :=
    preservesColimitsOfShape_of_natIso e.symm
  exact preservesColimitsOfShape_of_reflects_of_preserves F V

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem brownSized
    {A : Type a} [Category.{w} A] [Abelian A]
    [IsGrothendieckAbelian.{w} A] [hDA : HasDerivedCategory.{dA} A]
    {B : Type b} [Category.{w} B] [Abelian B]
    [IsGrothendieckAbelian.{w} B] [hDB : HasDerivedCategory.{dB} B]
    [HasCoproducts.{w} (DerivedCategory A)] [HasCoproducts.{w} (DerivedCategory B)]
    (F : DerivedCategory A ⥤ DerivedCategory B) [F.CommShift ℤ] [F.IsTriangulated]
    (hF : ∀ I : Type w, PreservesColimitsOfShape (Discrete I) F) :
    F.IsLeftAdjoint := by
  let hA : HasDerivedCategory.{w} A := HasDerivedCategory.ofIsGrothendieckAbelian A
  let hB : HasDerivedCategory.{w} B := HasDerivedCategory.ofIsGrothendieckAbelian B
  let := hA
  let := hB
  let U := @Functor.mapDerivedCategory A _ _ hA A _ _ hDA (𝟭 A) _ _ _
  let V := @Functor.mapDerivedCategory B _ _ hDB B _ _ hB (𝟭 B) _ _ _
  have : U.IsEquivalence :=
    @Functor.isEquivalence_mapDerivedCategory A A _ _ _ _ hA hDA (𝟭 A) _ _
  have : V.IsEquivalence :=
    @Functor.isEquivalence_mapDerivedCategory B B _ _ _ _ hDB hB (𝟭 B) _ _
  let : U.CommShift ℤ := inferInstance
  have : ∀ n : ℤ, (shiftFunctor (@DerivedCategory A _ _ hA) n).Additive := by
    let := hA
    infer_instance
  have : ∀ n : ℤ, (shiftFunctor (@DerivedCategory A _ _ hDA) n).Additive := by
    let := hDA
    infer_instance
  have : U.IsTriangulated := inferInstance
  let : V.CommShift ℤ := inferInstance
  have : ∀ n : ℤ, (shiftFunctor (@DerivedCategory B _ _ hB) n).Additive := by
    let := hB
    infer_instance
  have : ∀ n : ℤ, (shiftFunctor (@DerivedCategory B _ _ hDB) n).Additive := by
    let := hDB
    infer_instance
  have : V.IsTriangulated := inferInstance
  let H := (U ⋙ F) ⋙ V
  let : H.CommShift ℤ := inferInstance
  have : H.IsTriangulated := inferInstance
  have hH (I : Type w) : PreservesColimitsOfShape (Discrete I) H := by
    have := hF I
    infer_instance
  have : H.IsLeftAdjoint := by
    let := hA
    let := hB
    have : HasCoproducts.{w} A := inferInstance
    have : HasCoproducts.{w} B := inferInstance
    have : HasCoproducts.{w} (@DerivedCategory A _ _ hA) := derived_hasCoproducts
    have : HasCoproducts.{w} (@DerivedCategory B _ _ hB) := derived_hasCoproducts
    exact grothendieckDerived_hasRightAdjoint H hH
  exact (Functor.isLeftAdjoint_comp_iff_right U F).mp
    ((Functor.isLeftAdjoint_comp_iff_left (U ⋙ F) V).mp inferInstance)

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem towerExact {O : Type (u + 1)} [CommRing O] {t : O}
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
    (S : StrictEtaleCompactSupport O t c) :
    ∃ (_ : S.functor.Additive) (s : S.functor.CommShift ℤ), letI := s;
      S.functor.IsTriangulated := by
  let : S.openImage.inverse.Additive := S.openImage.systemInverseAdditive
  let : S.properImage.inverse.Additive := S.properImage.systemInverseAdditive
  let : S.openImage.rightSystem.Additive := S.openImage.systemRightAdditive
  let : S.properImage.rightSystem.Additive := S.properImage.systemRightAdditive
  have := S.openImage.systemExact.1
  have := S.openImage.systemExact.2
  have := S.properImage.systemExact.1
  have := S.properImage.systemExact.2
  let eo := exactDerivedIso S.openImage.inverse S.openDerived.system.inverse
    S.openDerived.system.inverseFactors
  let ep := exactDerivedIso S.properImage.inverse S.properDerived.system.inverse
    S.properDerived.system.inverseFactors
  let : S.openDerived.system.inverse.CommShift ℤ := CommShift.ofIso eo.symm ℤ
  let : S.properDerived.system.inverse.CommShift ℤ := CommShift.ofIso ep.symm ℤ
  have : NatTrans.CommShift eo.symm.hom ℤ := CommShift.ofIso_compatibility eo.symm ℤ
  have : NatTrans.CommShift ep.symm.hom ℤ := CommShift.ofIso_compatibility ep.symm ℤ
  have : S.openDerived.system.inverse.IsTriangulated :=
    isTriangulated_of_iso eo.symm
  have : S.properDerived.system.inverse.IsTriangulated :=
    isTriangulated_of_iso ep.symm
  have : S.openDerived.system.inverse.Additive := additive_of_iso eo.symm
  have : S.properDerived.system.inverse.Additive := additive_of_iso ep.symm
  let : S.derivedOpen.CommShift ℤ := S.derivedOpenAdjunction.leftAdjointCommShift ℤ
  have : S.derivedOpenAdjunction.CommShift ℤ :=
    S.derivedOpenAdjunction.commShift_of_rightAdjoint ℤ
  have : S.derivedOpen.IsTriangulated := S.derivedOpenAdjunction.isTriangulated_leftAdjoint
  have : S.derivedOpen.Additive := S.derivedOpenAdjunction.left_adjoint_additive
  let : S.properDerived.system.direct.CommShift ℤ :=
    S.properDerived.system.adjunction.rightAdjointCommShift ℤ
  have : S.properDerived.system.adjunction.CommShift ℤ :=
    S.properDerived.system.adjunction.commShift_of_leftAdjoint ℤ
  have : S.properDerived.system.direct.IsTriangulated :=
    S.properDerived.system.adjunction.isTriangulated_rightAdjoint
  have : S.properDerived.system.direct.Additive :=
    S.properDerived.system.adjunction.right_adjoint_additive
  change ∃ (_ : (S.derivedOpen ⋙ S.properDerived.system.direct).Additive)
    (s : (S.derivedOpen ⋙ S.properDerived.system.direct).CommShift ℤ), letI := s;
    (S.derivedOpen ⋙ S.properDerived.system.direct).IsTriangulated
  exact ⟨inferInstance, inferInstance, inferInstance⟩

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem scalar_adjunction {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] {F : C ⥤ D} {G : D ⥤ C}
    (adj : F ⊣ G) (s : 𝟭 C ⟶ 𝟭 C) (t : 𝟭 D ⟶ 𝟭 D)
    (h : ∀ K, F.map (s.app K) = t.app (F.obj K)) :
    (∀ K L (a : F.obj K ⟶ L),
      adj.homEquiv K L (t.app (F.obj K) ≫ a) = s.app K ≫ adj.homEquiv K L a) ∧
    (∀ L, adj.homEquiv (G.obj L) L (t.app (F.obj (G.obj L)) ≫
      adj.counit.app L) = s.app (G.obj L)) ∧
    (∀ L, G.map (t.app L) = s.app (G.obj L)) := by
  have hh (K : C) (L : D) (a : F.obj K ⟶ L) :
      adj.homEquiv K L (t.app (F.obj K) ≫ a) = s.app K ≫ adj.homEquiv K L a := by
    rw [← h, adj.homEquiv_naturality_left]
    rfl
  refine ⟨hh, ?_, ?_⟩
  · intro L
    rw [hh]
    have hc : adj.homEquiv (G.obj L) L (adj.counit.app L) = 𝟙 _ := by
      rw [← adj.homEquiv_symm_id L]
      exact Equiv.apply_symm_apply _ _
    rw [hc]
    exact Category.comp_id _
  · intro L
    apply (adj.homEquiv (G.obj L) L).symm.injective
    simp only [Adjunction.homEquiv_counit, h]
    calc
      _ = adj.counit.app L ≫ t.app L := by
        simpa only [Functor.comp_map, Functor.id_map, Functor.id_obj, Functor.comp_obj]
          using adj.counit.naturality (t.app L)
      _ = _ := by
        simpa only [Functor.id_map, Functor.id_obj, Functor.comp_obj]
          using t.naturality (adj.counit.app L)

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private def brownComponents (W : Scheme.{u}) (O : Type (u + 1)) [CommRing O]
    (t : O) (P : StrictEtaleEvaluation W O t) : StrictEtaleBrownComponents O t W P := by
  let B := coefficientRings (J := W.smallEtaleTopology) (O := O) (ell := t)
  let e := coefficientSystemEquivalence (J := W.smallEtaleTopology) (O := O) (ell := t)
  have := strictRingSystem_isGrothendieckAbelian B
  have : IsGrothendieckAbelian.{u + 1} (strictEtaleCoefficientSystem W O t) :=
    IsGrothendieckAbelian.of_equivalence e.symm
  have : HasColimitsOfSize.{u + 1, u + 1} (strictEtaleCoefficientSystem W O t) :=
    IsGrothendieckAbelian.hasColimits _
  have hlim (n : ℕ) :=
    (coefficientEvaluation_exact (J := W.smallEtaleTopology) (O := O) (ell := t) n).1
  have hcolim (n : ℕ) :=
    (coefficientEvaluation_exact (J := W.smallEtaleTopology) (O := O) (ell := t) n).2
  have hord (n : ℕ) (I : Type (u + 1)) : PreservesColimitsOfShape (Discrete I)
      (coefficientEvaluation (J := W.smallEtaleTopology) (O := O) (ell := t) n) := by
    have := systemEvaluation_colimitsOfShape B (Discrete I) n
    change PreservesColimitsOfShape (Discrete I) (e.functor ⋙ systemEvaluation B n)
    infer_instance
  let cohom (n : ℕ) (q : ℤ) :=
    Functor.mapDerivedCategoryHomologyFunctorIso
      (coefficientEvaluation (J := W.smallEtaleTopology) (O := O) (ell := t) n) q ≪≫
        isoWhiskerRight (coefficientEvaluation_derivedIso O t P n).symm
          (DerivedCategory.homologyFunctor (strictEtaleLevel W O t n) q)
  have hzero (M : strictEtaleCoefficientSystem W O t) :
      IsZero M ↔ ∀ n : ℕ, IsZero (M.level n) := by
    constructor
    · intro h n
      exact (coefficientEvaluation (J := W.smallEtaleTopology)
        (O := O) (ell := t) n).map_isZero h
    · intro h
      apply (IsZero.iff_id_eq_zero M).2
      apply SheafOfModules.system_hom_ext O t
      funext n
      change (coefficientEvaluation (J := W.smallEtaleTopology)
        (O := O) (ell := t) n).map (𝟙 M) =
          (coefficientEvaluation (J := W.smallEtaleTopology)
            (O := O) (ell := t) n).map (0 : M ⟶ M)
      rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero]
      exact (IsZero.iff_id_eq_zero _).1 (h n)
  have hhom (M : DerivedCategory (strictEtaleCoefficientSystem W O t)) (q : ℤ) :
      IsZero ((DerivedCategory.homologyFunctor _ q).obj M) ↔
        ∀ n, IsZero ((DerivedCategory.homologyFunctor _ q).obj ((P.evaluation n).obj M)) := by
    rw [hzero]
    exact forall_congr' (fun n ↦ ((cohom n q).app M).isZero_iff)
  refine { grothendieck := inferInstance
           coproducts := inferInstance
           derivedCoproducts := derived_hasCoproducts
           ordinary := hord
           derived := ?_
           cohomology := cohom
           bounds := ?_ }
  · intro n I
    have : IsGrothendieckAbelian.{u + 1} (strictEtaleLevel W O t n) :=
      isGrothendieckAbelian_coefficientUniverse _
    have := hord n I
    have := (coefficientEvaluation (J := W.smallEtaleTopology)
      (O := O) (ell := t) n).mapDerivedCategory_preservesCoproducts I
    exact preservesColimitsOfShape_of_natIso (coefficientEvaluation_derivedIso O t P n).symm
  · intro M q
    constructor
    · simp only [DerivedCategory.isGE_iff, hhom]
      exact ⟨fun h n i hi ↦ h i hi n, fun h i hi n ↦ h n i hi⟩
    · simp only [DerivedCategory.isLE_iff, hhom]
      exact ⟨fun h n i hi ↦ h i hi n, fun h i hi n ↦ h n i hi⟩

attribute [local instance] CoefficientSystemOrdinaryImage.inverseAdditive
  CoefficientSystemOrdinaryImage.rightAdditive
  CoefficientSystemOrdinaryImage.systemInverseAdditive
  CoefficientSystemOrdinaryImage.systemRightAdditive

private theorem brownCoproducts {O : Type (u + 1)} [CommRing O] {t : O}
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
    (S : StrictEtaleCompactSupport O t c)
    (hX : StrictEtaleBrownComponents O t X S.PX)
    (hY : StrictEtaleBrownComponents O t Y S.PY)
    (hp : ∀ (n : ℕ) (I : Type (u + 1)),
      PreservesColimitsOfShape (Discrete I) (S.properDerived.level n).direct)
    (I : Type (u + 1)) : PreservesColimitsOfShape (Discrete I) S.functor := by
  have := hX.derivedCoproducts
  have := hY.derivedCoproducts
  have hE (n : ℕ) := hY.derived n I
  have hFE (n : ℕ) :
      PreservesColimitsOfShape (Discrete I) (S.functor ⋙ S.PY.evaluation n) := by
    have := hX.derived n I
    have := hp n I
    have : (S.levelDerivedOpen n).IsLeftAdjoint :=
      ⟨_, ⟨S.levelDerivedOpenAdjunction n⟩⟩
    have : PreservesColimitsOfShape (Discrete I) (S.levelFunctor n) := by
      change PreservesColimitsOfShape (Discrete I)
        (S.levelDerivedOpen n ⋙ (S.properDerived.level n).direct)
      infer_instance
    exact preservesColimitsOfShape_of_natIso (S.evaluation n).symm
  let hj : JointlyReflectIsomorphisms S.PY.evaluation :=
    ⟨fun a ha ↦ (coefficientEvaluation_detectsIso O t S.PY a).2 ha⟩
  constructor
  intro K
  apply preservesColimit_of_preserves_colimit_cocone (colimit.isColimit K)
  apply hj.jointlyReflectsColimit
  intro n
  exact isColimitOfPreserves (S.functor ⋙ S.PY.evaluation n) (colimit.isColimit K)

end AlgebraicGeometry
