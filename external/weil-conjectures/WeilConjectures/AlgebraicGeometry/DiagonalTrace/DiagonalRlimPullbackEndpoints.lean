/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTowerTraceCoefficients
public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerLimitInterface
public import WeilConjectures.AlgebraicGeometry.StrictTower.StrictConstantTowerOperationsSupplement
public import WeilConjectures.CategoryTheory.Ringed.RingedConstantTowerPushforwardNormalization
public import WeilConjectures.CategoryTheory.Derived.DerivedTowerCounitProjections
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Realization.DiagonalRealizationPullback
public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientTwistsSupplement
import WeilConjectures.AlgebraicGeometry.WeilSheaf.ProfiniteCoefficientInverseImageSupplement
import WeilConjectures.AlgebraicGeometry.Native.NativeIntegralTateTowerLimit
import WeilConjectures.AlgebraicGeometry.Pur.PurTwistRootTransitions
import WeilConjectures.CategoryTheory.SmoothPurity.CanonicalRightDerivedAdjunctionShift
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageScalarGraph
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Sites.Sheafification
import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import Mathlib.CategoryTheory.Monoidal.Ring
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import WeilConjectures.AlgebraicGeometry.ProEtaleModelRingPresentation
import WeilConjectures.CategoryTheory.SheafPullbackUnitPresentation
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
import WeilConjectures.CategoryTheory.ModuleInverseImageAdjunction
import WeilConjectures.CategoryTheory.ModuleInverseImageAction
import Mathlib.Algebra.Category.Ring.Limits
import WeilConjectures.CategoryTheory.ModuleInverseImageActionOfPresentations
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleAdjunction
import Mathlib.Algebra.Category.Ring.FilteredColimits
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageUnderlying
import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
import WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import WeilConjectures.CategoryTheory.Ringed.RingedStrictTowerHomotopyLimitOfUniverses
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import Mathlib.CategoryTheory.Adjunction.Evaluation
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import Mathlib.Algebra.BigOperators.Ring.Finset
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTraceOrdinaryLimitEpi
import WeilConjectures.AlgebraicGeometry.ProEtale.Tate.ProEtaleTateTwists
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
import Mathlib.CategoryTheory.Localization.Predicate

/-! # Derived-limit pullback comparison with normalized endpoints
Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-prop-diagonal-tower/
`sk-prop-diagonal-tower-coefficients.proof.md`, paragraph (3), constant-system/right-derived-limit
comparison and its coefficient/root isomorphism
(blueprint: lem-sfb-diagonal-rlim-pullback-endpoints).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u a b c d va vb vc vd wa wb wc wd
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalTrace
open AlgebraicGeometry.ProEtale
open SpTowerClasses

/-- The actual exact inverse image of fixed discrete scalar sheaves.
Source: blueprint coefficient proof (3)
(blueprint: lem-sfb-diagonal-rlim-pullback-endpoints). -/
abbrev diagonalRlimPull (l : ℕ) [Fact l.Prime] {X S : Scheme.{u}} (f : X ⟶ S)
    [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S] :
    DiagonalMod l S ⥤ DiagonalMod l X :=
  upperStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) f

/-- Its strict termwise tower functor.
Source: blueprint coefficient proof (3)
(blueprint: lem-sfb-diagonal-rlim-pullback-endpoints). -/
abbrev diagonalRlimTowerPull (l : ℕ) [Fact l.Prime] {X S : Scheme.{u}} (f : X ⟶ S)
    [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S] :
    DiagonalSystems l S ⥤ DiagonalSystems l X :=
  (Functor.whiskeringRight ℕᵒᵖ (DiagonalMod l S) (DiagonalMod l X)).obj
    (diagonalRlimPull l f)

/-- Evaluation after termwise pullback, induced by the ordinary termwise identity.
Source: blueprint coefficient proof (3)
(blueprint: lem-sfb-diagonal-rlim-pullback-endpoints). -/
def diagonalRlimPullbackEvaluation (l : ℕ) [Fact l.Prime] {X S : Scheme.{u}} (f : X ⟶ S)
    [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S] (n : ℕ) :
    (diagonalRlimTowerPull l f).mapDerivedCategory ⋙
      ((evaluation ℕᵒᵖ (DiagonalMod l X)).obj (op n)).mapDerivedCategory ≅
    ((evaluation ℕᵒᵖ (DiagonalMod l S)).obj (op n)).mapDerivedCategory ⋙
      (diagonalRlimPull l f).mapDerivedCategory :=
  Functor.mapDerivedCategoryCompIso (diagonalRlimTowerPull l f)
    ((evaluation ℕᵒᵖ (DiagonalMod l X)).obj (op n)) ≪≫
  Functor.mapDerivedCategoryNatIso (eqToIso rfl) ≪≫
  (Functor.mapDerivedCategoryCompIso
    ((evaluation ℕᵒᵖ (DiagonalMod l S)).obj (op n)) (diagonalRlimPull l f)).symm

/-- The mate uses the canonical identity-on-components constant-tower interchange.
Source: blueprint coefficient proof (3)
(blueprint: lem-sfb-diagonal-rlim-pullback-endpoints). -/
def diagonalRlimPullbackMate (l : ℕ) [Fact l.Prime] {X S : Scheme.{u}} (f : X ⟶ S)
    [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S]
    (LX : DiagonalRlim (DiagonalMod l X)) (LS : DiagonalRlim (DiagonalMod l S))
    (adjX : (Functor.const ℕᵒᵖ : DiagonalMod l X ⥤ DiagonalSystems l X).mapDerivedCategory ⊣ LX.R)
    (adjS : (Functor.const ℕᵒᵖ : DiagonalMod l S ⥤ DiagonalSystems l S).mapDerivedCategory ⊣ LS.R) :
    LS.R ⋙ (diagonalRlimPull l f).mapDerivedCategory ⟶
      (diagonalRlimTowerPull l f).mapDerivedCategory ⋙ LX.R :=
  (mateEquiv adjS adjX (TwoSquare.mk _ _ _ _
    (ringedConstantTowerPullback (diagonalRlimPull l f)).inv))

/-- The full pulled cone, using the canonical constant-tower interchange.
Source: blueprint coefficient proof (3), ordinary cone normalization
(blueprint: lem-sfb-diagonal-rlim-pullback-endpoints). -/
def diagonalRlimPulledCone (l : ℕ) [Fact l.Prime] {X S : Scheme.{u}} (f : X ⟶ S)
    [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S]
    (M : DiagonalMod l S) (H : DiagonalSystems l S)
    (π : (Functor.const ℕᵒᵖ).obj M ⟶ H) :
    (Functor.const ℕᵒᵖ).obj ((diagonalRlimPull l f).obj M) ⟶
      (diagonalRlimTowerPull l f).obj H :=
  (Functor.compConstIso ℕᵒᵖ (diagonalRlimPull l f)).hom.app M ≫
    (diagonalRlimTowerPull l f).map π

/-- Pull back an exact scalar cone, retaining the canonical derived composition maps.
Source: blueprint coefficient proof (3), scalar restriction and endpoint cones
(blueprint: lem-sfb-diagonal-rlim-pullback-endpoints). -/
def diagonalRlimPulledScalarConeMap (l : ℕ) [Fact l.Prime] {X S : Scheme.{u}}
    (f : X ⟶ S) [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S]
    (LX : DiagonalRlim (DiagonalMod l X))
    (r : Restriction l (ULift.{u} (Padic l)) S)
    (M : DiagonalCompleted l S) (N : Systems S (Arings l (ULift.{u} (Padic l)) S))
    (π : (Functor.const ℕᵒᵖ).obj ((diagonalCompletedRestriction l S).obj M) ⟶ r.F.obj N) :
    (diagonalCompletedUnderlying l S ⋙ (diagonalRlimPull l f).mapDerivedCategory).obj
        ((DerivedCategory.singleFunctor (DiagonalCompleted l S) 0).obj M) ⟶
      (r.F.mapDerivedCategory ⋙ (diagonalRlimTowerPull l f).mapDerivedCategory ⋙ LX.R).obj
        ((DerivedCategory.singleFunctor (Systems S (Arings l (ULift.{u} (Padic l)) S))
          0).obj N) :=
  (Functor.mapDerivedCategoryCompIso (diagonalCompletedRestriction l S)
    (diagonalRlimPull l f)).hom.app _ ≫
  exactConeComparison (diagonalCompletedRestriction l S ⋙ diagonalRlimPull l f)
    (r.F ⋙ diagonalRlimTowerPull l f) LX M N
    (diagonalRlimPulledCone l f _ _ π) ≫
  LX.R.map ((Functor.mapDerivedCategoryCompIso r.F
    (diagonalRlimTowerPull l f)).inv.app _)

/-- Canonical localization of an exact scalar/pullback square.
Source: blueprint coefficient proof (3), exact restriction squares
(blueprint: lem-sfb-diagonal-rlim-pullback-endpoints). -/
def diagonalRlimExactSquare
    {A : Type a} {B : Type b} {C : Type c} {D : Type d}
    [Category.{va} A] [Category.{vb} B] [Category.{vc} C] [Category.{vd} D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory.{wa} A] [HasDerivedCategory.{wb} B]
    [HasDerivedCategory.{wc} C] [HasDerivedCategory.{wd} D]
    (U : A ⥤ B) (F : B ⥤ D) (G : A ⥤ C) (V : C ⥤ D)
    [U.Additive] [F.Additive] [G.Additive] [V.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (s : U ⋙ F ≅ G ⋙ V) :
    U.mapDerivedCategory ⋙ F.mapDerivedCategory ≅
      G.mapDerivedCategory ⋙ V.mapDerivedCategory :=
  Functor.mapDerivedCategoryCompIso U F ≪≫
    Functor.mapDerivedCategoryNatIso s ≪≫ (Functor.mapDerivedCategoryCompIso G V).symm

/-- Localize the varying scalar square using its recorded exact inverse image.
Source: blueprint coefficient proof (3), varying scalar restriction
(blueprint: lem-sfb-diagonal-rlim-pullback-endpoints). -/
def diagonalRlimVaryingSquare (l : ℕ) [Fact l.Prime] {X S : Scheme.{u}}
    (f : X ⟶ S) [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S]
    (b : SpTowerShriek.Base l (ULift.{u} (Padic l)))
    (g : SpTowerShriek.Geometry l (ULift.{u} (Padic l)) b f)
    (rS : Restriction l (ULift.{u} (Padic l)) S)
    (rX : Restriction l (ULift.{u} (Padic l)) X)
    (v : rS.F ⋙ diagonalRlimTowerPull l f ≅ g.pull ⋙ rX.F) :
    rS.F.mapDerivedCategory ⋙ (diagonalRlimTowerPull l f).mapDerivedCategory ≅
      (SpTowerShriek.pull l (ULift.{u} (Padic l)) b g) ⋙ rX.F.mapDerivedCategory := by
  letI := g.pullAdditive
  letI := g.pullLimits
  letI := g.pullColimits
  letI := rS.additive
  letI := rX.additive
  letI := rS.limits
  letI := rX.limits
  letI := rS.colimits
  letI := rX.colimits
  exact diagonalRlimExactSquare rS.F (diagonalRlimTowerPull l f) g.pull rX.F v

-- The statement writes `ℕᵒᵖ ⥤ DiagonalMod l _` rather than the abbreviation `DiagonalSystems l _`,
-- matching the types of the `DiagonalRlim` fields, and writes the cone conjunct with the
-- `whiskeringRight` functor of `LocalChernConeMate`. Mixed spellings under projections such as
-- `Functor.obj` make the kernel unfold derived-category functors on every comparison.
/-- The normalized mate on the actual quotient and root towers, its full ordinary cones,
shifted coefficient and root-line arrows, scalar restrictions, and derived morphisms.
Source: blueprint coefficient proof (3).

Proof plan:
1. Use derived_tower_counit_projections to normalize the constant/limit adjunctions.
   The full counit on K-injective towers is the ordinary cone; its evaluation is the
   specified derived projection. These equations exclude sign-modified adjunctions.
2. Transpose the canonical constant-tower interchange followed by the source counit.
   Adjunction injectivity gives the counit equation. Evaluation gives every finite
   projection equation; naturality of the mate gives equality before evaluation.
3. For an ordinary cone transpose both routes into the pulled derived limit. Both
   transposes are its full pulled strict cone, so the routes agree. No faithfulness
   of derived evaluation is used. Apply this to the coefficient and root cones in aS.
4. The coefficientForget and lineForget fields identify the two specified towers with
   (Z/l^(n+1))_S and mu_(l^(n+1),S), including transitions and unit/root normalization.
   Profinite coefficient inverse image preserves the coefficient limit and quotients.
   Cartesian integral Tate pullback preserves the root limit and every root projection.
5. Quotient and power transitions are epic. Apply new-sfb-diagonal-trace-ordinary-rlim-epi
   on both schemes. The ordinary-to-derived comparisons are invertible; step 3 then
   expresses the mate as a composite of these maps and the ordinary limit isomorphism.
6. The scalar squares commute on each scalar, with residue action at each finite level.
   The underlying-sheaf adjunction equations fix the exact restriction/pullback squares.
   Localize those exact comparisons to obtain the derived scalar squares.
7. Insert the canonical single comparisons into step 3. By exactConeComparison this is
   the coefficient-unit/lineMap equation. The normalized cones give every endpoint.
8. The normalized unit, constant/limit adjunction, exact inverse image and restrictions
   commute with canonical shifts. Transpose after shifting; injectivity gives the shift
   equation, hence the shifted endpoint equations and compatibility with Chern arrows.
(blueprint: lem-sfb-diagonal-rlim-pullback-endpoints). -/
theorem diagonalRlim_pullback_endpoints (l : ℕ) [Fact l.Prime] {X S : Scheme.{u}} (f : X ⟶ S)
    [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : S, Invertible (l : S.residueField y)]
    (LX : DiagonalRlim (DiagonalMod l X)) (LS : DiagonalRlim (DiagonalMod l S))
    (adjX : (Functor.const ℕᵒᵖ : DiagonalMod l X ⥤ ℕᵒᵖ ⥤ DiagonalMod l X).mapDerivedCategory ⊣
      LX.R)
    (adjS : (Functor.const ℕᵒᵖ : DiagonalMod l S ⥤ ℕᵒᵖ ⥤ DiagonalMod l S).mapDerivedCategory ⊣
      LS.R)
    (hCounitX : ∀ (I : CochainComplex (ℕᵒᵖ ⥤ DiagonalMod l X) ℤ), I.IsKInjective →
      (Functor.const ℕᵒᵖ : DiagonalMod l X ⥤ ℕᵒᵖ ⥤ DiagonalMod l X).mapDerivedCategory.map
          (LX.η.app I) ≫ adjX.counit.app (DerivedCategory.Q.obj I) =
        (Functor.const ℕᵒᵖ : DiagonalMod l X ⥤
          ℕᵒᵖ ⥤ DiagonalMod l X).mapDerivedCategoryFactors.hom.app
          (((lim : (ℕᵒᵖ ⥤ DiagonalMod l X) ⥤ DiagonalMod l X).mapHomologicalComplex (.up ℤ)).obj
            I) ≫
        DerivedCategory.Q.map
          ((Adjunction.mapHomologicalComplex (.up ℤ)
            (constLimAdj : (Functor.const ℕᵒᵖ : DiagonalMod l X ⥤ ℕᵒᵖ ⥤ DiagonalMod l X) ⊣
              lim)).counit.app I))
    (hProjectionX : ∀ (n : ℕ) (K : DerivedCategory (ℕᵒᵖ ⥤ DiagonalMod l X)),
      ((evaluation ℕᵒᵖ (DiagonalMod l X)).obj (op n)).mapDerivedCategory.map (adjX.counit.app K) =
        (ringedConstantTowerEvaluation (DiagonalMod l X) (op n)).hom.app (LX.R.obj K) ≫
          (LX.projection n).app K)
    (hCounitS : ∀ (I : CochainComplex (ℕᵒᵖ ⥤ DiagonalMod l S) ℤ), I.IsKInjective →
      (Functor.const ℕᵒᵖ : DiagonalMod l S ⥤ ℕᵒᵖ ⥤ DiagonalMod l S).mapDerivedCategory.map
          (LS.η.app I) ≫ adjS.counit.app (DerivedCategory.Q.obj I) =
        (Functor.const ℕᵒᵖ : DiagonalMod l S ⥤
          ℕᵒᵖ ⥤ DiagonalMod l S).mapDerivedCategoryFactors.hom.app
          (((lim : (ℕᵒᵖ ⥤ DiagonalMod l S) ⥤ DiagonalMod l S).mapHomologicalComplex (.up ℤ)).obj
            I) ≫
        DerivedCategory.Q.map
          ((Adjunction.mapHomologicalComplex (.up ℤ)
            (constLimAdj : (Functor.const ℕᵒᵖ : DiagonalMod l S ⥤ ℕᵒᵖ ⥤ DiagonalMod l S) ⊣
              lim)).counit.app I))
    (hProjectionS : ∀ (n : ℕ) (K : DerivedCategory (ℕᵒᵖ ⥤ DiagonalMod l S)),
      ((evaluation ℕᵒᵖ (DiagonalMod l S)).obj (op n)).mapDerivedCategory.map (adjS.counit.app K) =
        (ringedConstantTowerEvaluation (DiagonalMod l S) (op n)).hom.app (LS.R.obj K) ≫
          (LS.projection n).app K)
    (cS : Chern l (ULift.{u} (Padic l)) S)
    (rS : Restriction l (ULift.{u} (Padic l)) S)
    (aS : Coefficients l (ULift.{u} (Padic l)) S cS rS) :
    (∀ (K : DerivedCategory (ℕᵒᵖ ⥤ DiagonalMod l S)) (n : ℕ),
      (diagonalRlimPullbackMate l f LX LS adjX adjS).app K ≫
          (LX.projection n).app ((diagonalRlimTowerPull l f).mapDerivedCategory.obj K) ≫
          (diagonalRlimPullbackEvaluation l f n).hom.app K =
        (diagonalRlimPull l f).mapDerivedCategory.map ((LS.projection n).app K)) ∧
    IsIso ((diagonalRlimPullbackMate l f LX LS adjX adjS).app
      ((DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ DiagonalMod l S) 0).obj
        (rS.F.obj (coefficient S (Arings l (ULift.{u} (Padic l)) S))))) ∧
    IsIso ((diagonalRlimPullbackMate l f LX LS adjX adjS).app
      ((DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ DiagonalMod l S) 0).obj
        (rS.F.obj (lineModule l (ULift.{u} (Padic l)) cS)))) ∧
    (∀ (H : ℕᵒᵖ ⥤ DiagonalMod l S) (c : Cone H),
      (diagonalRlimPull l f).mapDerivedCategory.map (diagonalTraceConeMap LS H c) ≫
          (diagonalRlimPullbackMate l f LX LS adjX adjS).app
            ((DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ DiagonalMod l S) 0).obj H) ≫
          LX.R.map ((((Functor.whiskeringRight ℕᵒᵖ (DiagonalMod l S) (DiagonalMod l X)).obj
            (diagonalRlimPull l f)).mapDerivedCategorySingleFunctor 0).hom.app H) =
        ((diagonalRlimPull l f).mapDerivedCategorySingleFunctor 0).hom.app c.pt ≫
          diagonalTraceConeMap LX
            (((Functor.whiskeringRight ℕᵒᵖ (DiagonalMod l S) (DiagonalMod l X)).obj
              (diagonalRlimPull l f)).obj H)
            ((diagonalRlimPull l f).mapCone c)) ∧
    (∀ m : ℤ,
      shiftedComparison
        (diagonalCompletedUnderlying l S ⋙ (diagonalRlimPull l f).mapDerivedCategory)
        (rS.F.mapDerivedCategory ⋙ (diagonalRlimTowerPull l f).mapDerivedCategory ⋙ LX.R)
        ((diagonalRlimPull l f).mapDerivedCategory.map (aS.unitMap l (ULift.{u} (Padic l)) LS) ≫
          (diagonalRlimPullbackMate l f LX LS adjX adjS).app
            (rS.F.mapDerivedCategory.obj (unit S (Arings l (ULift.{u} (Padic l)) S)))) m =
      shiftedComparison
        (diagonalCompletedUnderlying l S ⋙ (diagonalRlimPull l f).mapDerivedCategory)
        (rS.F.mapDerivedCategory ⋙ (diagonalRlimTowerPull l f).mapDerivedCategory ⋙ LX.R)
        (diagonalRlimPulledScalarConeMap l f LX rS
          (SheafOfModules.unit (Scheme.purTwistRing S (Scheme.purTwistZlCompletion S l)))
          (coefficient S (Arings l (ULift.{u} (Padic l)) S)) aS.coefficientProjection) m) ∧
    (∀ m : ℤ,
      shiftedComparison
        (diagonalCompletedUnderlying l S ⋙ (diagonalRlimPull l f).mapDerivedCategory)
        (rS.F.mapDerivedCategory ⋙ (diagonalRlimTowerPull l f).mapDerivedCategory ⋙ LX.R)
        ((diagonalRlimPull l f).mapDerivedCategory.map (aS.lineMap l (ULift.{u} (Padic l)) LS) ≫
          (diagonalRlimPullbackMate l f LX LS adjX adjS).app
            (rS.F.mapDerivedCategory.obj (line l (ULift.{u} (Padic l)) cS))) m =
      shiftedComparison
        (diagonalCompletedUnderlying l S ⋙ (diagonalRlimPull l f).mapDerivedCategory)
        (rS.F.mapDerivedCategory ⋙ (diagonalRlimTowerPull l f).mapDerivedCategory ⋙ LX.R)
        (diagonalRlimPulledScalarConeMap l f LX rS
          (Scheme.purTwistZlModule S l)
          (lineModule l (ULift.{u} (Padic l)) cS) aS.lineProjection) m) ∧
    (∀ (b : SpTowerShriek.Base l (ULift.{u} (Padic l)))
        (g : SpTowerShriek.Geometry l (ULift.{u} (Padic l)) b f)
        (rX : Restriction l (ULift.{u} (Padic l)) X),
      ∃ (d : g.push ⋙ rS.F ≅ rX.F ⋙ diagonalTraceSystemPush l f)
        (v : rS.F ⋙ diagonalRlimTowerPull l f ≅ g.pull ⋙ rX.F),
        (∀ (M : Systems X (Arings l (ULift.{u} (Padic l)) X)) (n : ℕ)
          (U : S.ProEtᵒᵖ)
          (x : (((g.push ⋙ rS.F).obj M).obj (op n)).obj.obj U),
          HEq (((d.hom.app M).app (op n)).hom.app U x) x) ∧
        (mateEquiv g.ordinaryAdjunction
          ((upperStarLowerStarAdjunction
            (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) f).whiskerRight ℕᵒᵖ)
          (TwoSquare.mk _ _ _ _ v.hom)) = d.hom ∧
        NatTrans.CommShift
          (diagonalRlimVaryingSquare l f b g rS rX v).hom ℤ) ∧
    (∃ (d : Scheme.proEtaleRingModuleDirectImage f
          (Scheme.purTwistZlCompletion S l) (Scheme.purTwistZlCompletion X l)
          (asIso (diagonalCompletedCoefficientMap l f)) ⋙ diagonalCompletedRestriction l S ≅
        diagonalCompletedRestriction l X ⋙
          lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) f)
      (v : diagonalCompletedRestriction l S ⋙ diagonalRlimPull l f ≅
        DiagonalCoefficients.diagonalRealizationPull l f ⋙ diagonalCompletedRestriction l X),
      (∀ (M : DiagonalCompleted l X) (U : S.ProEtᵒᵖ)
        (x : ((Scheme.proEtaleRingModuleDirectImage f
          (Scheme.purTwistZlCompletion S l) (Scheme.purTwistZlCompletion X l)
          (asIso (diagonalCompletedCoefficientMap l f)) ⋙
          diagonalCompletedRestriction l S).obj M).obj.obj U),
        HEq ((d.hom.app M).hom.app U x) x) ∧
      (mateEquiv (Scheme.proEtaleRingModuleAdjunction f
          (Scheme.purTwistZlCompletion S l) (Scheme.purTwistZlCompletion X l)
          (asIso (diagonalCompletedCoefficientMap l f)))
        (upperStarLowerStarAdjunction
          (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) f)
        (TwoSquare.mk _ _ _ _ v.hom)) = d.hom ∧
      NatTrans.CommShift (diagonalRlimExactSquare (diagonalCompletedRestriction l S)
        (diagonalRlimPull l f) (DiagonalCoefficients.diagonalRealizationPull l f)
        (diagonalCompletedRestriction l X) v).hom ℤ) ∧
    NatTrans.CommShift (diagonalRlimPullbackMate l f LX LS adjX adjS) ℤ ∧
    (∀ {K K' : DerivedCategory (ℕᵒᵖ ⥤ DiagonalMod l S)} (z : K ⟶ K'),
      (LS.R ⋙ (diagonalRlimPull l f).mapDerivedCategory).map z ≫
          (diagonalRlimPullbackMate l f LX LS adjX adjS).app K' =
        (diagonalRlimPullbackMate l f LX LS adjX adjS).app K ≫
          ((diagonalRlimTowerPull l f).mapDerivedCategory ⋙ LX.R).map z) := by
  sorry

end AlgebraicGeometry.ProEtale.DiagonalTrace
