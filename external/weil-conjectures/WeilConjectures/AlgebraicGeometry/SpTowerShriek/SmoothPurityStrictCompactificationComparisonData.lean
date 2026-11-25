/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityTowerShriekData
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityTowerInjectiveComponents
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
public import WeilConjectures.AlgebraicGeometry.Compact.CompactSupportExchangeTransport
public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenTensorNormalizationData
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekProjection

/-!
# Normalized strict-tower compactification comparisons

Source: blueprint main-20261015, sec-smooth-purity/sk-lem-sp-tower-bound,
`sk-lem-sp-tower-bound-operations.proof.md`, paragraph (2).
(blueprint: def-sp-strict-compactification-comparison-interfaces).

The existing SpTowerShriek interfaces name the strict quotient tower, its
identity-section presentation, and the actual counit/open-mate words. No
invertibility of a proper projection or exchange is included here. Level n in
this module means the positive exponent n+1.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genCtorIdx false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor
  HasDerivedCategory.standard
  Padic Padic.coefficientExtensionIntegers
  SheafOfModules.OpenTensorNormalization.finiteTensor
attribute [local instance 100] HasDerivedCategory.standard

universe u c₁ c₂ c₃ c₄ v₁ v₂ v₃ v₄

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures

namespace AlgebraicGeometry.ProEtale.SpTowerShriek

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The induced equivalence on ordinary derived categories of the actual
strict towers. Both functors are exact localization of the identity-section
presentation and its inverse. Source: blueprint operations proof (2)
(blueprint: def-sp-strict-compactification-comparison-interfaces). -/
def comparisonTowerEquivalence (b : Base l E) (T : Scheme.{u}) :
    DerivedCategory (spCoefficientTowers l E T) ≌ D l E T := by
  letI := b.realizationAdditive T
  letI : (b.realization T).inverse.Additive :=
    Functor.additive_of_preserves_binary_products _
  exact (b.realization T).mapDerivedCategory

/-- Tensor at an actual coefficient level, using the existing K-flat total model.
Source: blueprint operations proof (2)
(blueprint: def-sp-strict-compactification-comparison-interfaces). -/
abbrev comparisonLevelTensor (b : Base l E) (T : Scheme.{u}) (n : ℕ) :=
  (b.calculus T).levelClosed n |>.tensor

/-- The normalized finite open adjunction, obtained from the actual ordinary
section adjunction by exact localization. Source: blueprint operations proof (2)
(blueprint: def-sp-strict-compactification-comparison-interfaces). -/
def comparisonLevelOpenAdjunction (b : Base l E) {U T : Scheme.{u}}
    (j : U ⟶ T) [IsOpenImmersion j] (n : ℕ) :
    @sfIntrinsicDerivedOpen (R l E n) _ (b.finite n) _ _ j _ ⊣
      proEtaleConstantRingDerivedPullback (R l E n) j := by
  letI := b.finite n
  letI := sfIntrinsicExtensionByZero_additive j (R l E n)
  letI := sfIntrinsicExtensionByZero_preservesFiniteLimits j (R l E n)
  letI := sfIntrinsicExtensionByZero_preservesFiniteColimits j (R l E n)
  letI : CatCommSq
      ((sfIntrinsicExtensionByZero j (R l E n)).mapHomologicalComplex (.up ℤ))
      DerivedCategory.Q DerivedCategory.Q
      (sfIntrinsicExtensionByZero j (R l E n)).mapDerivedCategory :=
    ⟨(sfIntrinsicExtensionByZero j (R l E n)).mapDerivedCategoryFactors.symm⟩
  letI : CatCommSq
      ((proEtaleConstantRingPullback (R l E n) j).mapHomologicalComplex (.up ℤ))
      DerivedCategory.Q DerivedCategory.Q
      (proEtaleConstantRingPullback (R l E n) j).mapDerivedCategory :=
    ⟨(proEtaleConstantRingPullback (R l E n) j).mapDerivedCategoryFactors.symm⟩
  exact ((finiteOpenAdjunction l E b j n).mapHomologicalComplex (.up ℤ)).localization
    DerivedCategory.Q (HomologicalComplex.quasiIso _ (.up ℤ))
    DerivedCategory.Q (HomologicalComplex.quasiIso _ (.up ℤ))
    (sfIntrinsicExtensionByZero j (R l E n)).mapDerivedCategory
    (proEtaleConstantRingPullback (R l E n) j).mapDerivedCategory

/-- Finite counterparts of the open and tensor comparisons. The inverse open
maps are fixed by their adjunction transposes, and the geometric tensor map is
fixed by the existing pure-tensor and total-complex normalization.
Source: blueprint operations proof (2), the finite adjunction words
(blueprint: def-sp-strict-compactification-comparison-interfaces). -/
structure ComparisonLevels (b : Base l E) (o : Operations l E b) where
  tensorPullback : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ),
    comparisonLevelTensor l E b Y n ⋙ proEtaleConstantRingDerivedPullback (R l E n) f ≅
      ((proEtaleConstantRingDerivedPullback (R l E n) f).prod
        (proEtaleConstantRingDerivedPullback (R l E n) f)) ⋙
          comparisonLevelTensor l E b X n
  tensorPullback_normalized : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ),
    HEq (tensorPullback f n) ((o.geometry f).generic.levelTensorPullback n)
  openTensor : ∀ {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j]
    (n : ℕ)
    (K : proEtaleDerivedCategory U (R l E n))
    (L : proEtaleDerivedCategory T (R l E n)),
    (comparisonLevelTensor l E b T n).obj ((sfIntrinsicDerivedOpen (R l E n) j).obj K, L) ≅
      (sfIntrinsicDerivedOpen (R l E n) j).obj
        ((comparisonLevelTensor l E b U n).obj
          (K, (proEtaleConstantRingDerivedPullback (R l E n) j).obj L))
  openTensor_mate : ∀ {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j]
    (n : ℕ) (K : proEtaleDerivedCategory U (R l E n))
    (L : proEtaleDerivedCategory T (R l E n)),
    ((comparisonLevelOpenAdjunction l E b j n).homEquiv _ _)
        ((openTensor j n K L).inv) =
      (comparisonLevelTensor l E b U n).map
          (Prod.mkHom ((comparisonLevelOpenAdjunction l E b j n).unit.app K) (𝟙 _)) ≫
        (tensorPullback j n).inv.app ((sfIntrinsicDerivedOpen (R l E n) j).obj K, L)
  openExchange : ∀ {U' U T' T : Scheme.{u}} (h : U' ⟶ U) (j' : U' ⟶ T')
    (j : U ⟶ T) (g : T' ⟶ T) [IsOpenImmersion j] [IsOpenImmersion j']
    (_sq : IsPullback h j' j g) (n : ℕ),
    sfIntrinsicDerivedOpen (R l E n) j ⋙
        proEtaleConstantRingDerivedPullback (R l E n) g ≅
      proEtaleConstantRingDerivedPullback (R l E n) h ⋙
        sfIntrinsicDerivedOpen (R l E n) j'
  openExchange_mate : ∀ {U' U T' T : Scheme.{u}} (h : U' ⟶ U) (j' : U' ⟶ T')
    (j : U ⟶ T) (g : T' ⟶ T) [IsOpenImmersion j] [IsOpenImmersion j']
    (sq : IsPullback h j' j g) (n : ℕ)
    (K : proEtaleDerivedCategory U (R l E n)),
    ((comparisonLevelOpenAdjunction l E b j' n).homEquiv _ _)
        ((openExchange h j' j g sq n).inv.app K) =
      (proEtaleConstantRingDerivedPullback (R l E n) h).map
          ((comparisonLevelOpenAdjunction l E b j n).unit.app K) ≫
        ((proEtaleConstantRingPullbackComposition h j (R l E n)).hom ≫
          eqToHom (congrArg (fun a ↦ proEtaleConstantRingDerivedPullback (R l E n) a)
            sq.w) ≫
          (proEtaleConstantRingPullbackComposition j' g (R l E n)).inv).app
            ((sfIntrinsicDerivedOpen (R l E n) j).obj K)

/-- The finite compactification projection, with exactly the proper counit,
open tensor comparison, and pullback compositor in that order.
Source: blueprint operations proof (2); def-exchange-projection
(blueprint: def-sp-strict-compactification-comparison-interfaces). -/
def comparisonLevelProjection (b : Base l E) (o : Operations l E b)
    (a : ComparisonLevels l E b o) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (n : ℕ)
    (K : proEtaleDerivedCategory X (R l E n))
    (L : proEtaleDerivedCategory Y (R l E n)) :
    (comparisonLevelTensor l E b Y n).obj ((finiteF l E b c n).obj K, L) ⟶
      (finiteF l E b c n).obj ((comparisonLevelTensor l E b X n).obj
        (K, (proEtaleConstantRingDerivedPullback (R l E n) f).obj L)) :=
  ((Adjunction.mapDerivedCategoryRightDerivedAdjunction
      (proEtaleConstantRingAdjunction (R l E n) c.g)).homEquiv _ _)
      ((a.tensorPullback c.g n).hom.app ((finiteF l E b c n).obj K, L) ≫
        (comparisonLevelTensor l E b c.Z n).map
          (Prod.mkHom
            ((Adjunction.mapDerivedCategoryRightDerivedAdjunction
              (proEtaleConstantRingAdjunction (R l E n) c.g)).counit.app
                ((sfIntrinsicDerivedOpen (R l E n) c.i).obj K)) (𝟙 _))) ≫
    (proEtaleConstantRingPushforward (R l E n) c.g).rightDerivedFunctor.map
      ((a.openTensor c.i n K
          ((proEtaleConstantRingDerivedPullback (R l E n) c.g).obj L)).hom ≫
        (sfIntrinsicDerivedOpen (R l E n) c.i).map
          ((comparisonLevelTensor l E b X n).map
            (Prod.mkHom (𝟙 K)
              (((proEtaleConstantRingPullbackComposition c.i c.g (R l E n)).hom ≫
                eqToHom (congrArg
                  (fun h ↦ proEtaleConstantRingDerivedPullback (R l E n) h)
                    c.comm.symm)).app L))))

/-- The finite compactification exchange, the same unit--square--counit--open
word as the tower exchange. Source: blueprint operations proof (2)
(blueprint: def-sp-strict-compactification-comparison-interfaces). -/
def comparisonLevelExchange (b : Base l E) (o : Operations l E b)
    (a : ComparisonLevels l E b o) {X' X Y' Y : Scheme.{u}}
    {h : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : IsPullback h f' f g) (c : Compactification f) (n : ℕ) :
    finiteF l E b c n ⋙ proEtaleConstantRingDerivedPullback (R l E n) g ⟶
      proEtaleConstantRingDerivedPullback (R l E n) h ⋙
        finiteF l E b (c.ofIsPullback sq) n :=
  CategoryTheory.SuppliedExchangeProjection.compactificationExchangeFromData
    (sfIntrinsicDerivedOpen (R l E n) c.i)
    (sfIntrinsicDerivedOpen (R l E n) (c.ofIsPullback sq).i)
    (proEtaleConstantRingDerivedPullback (R l E n) c.g)
    (proEtaleConstantRingPushforward (R l E n) c.g).rightDerivedFunctor
    (proEtaleConstantRingAdjunction (R l E n) c.g).mapDerivedCategoryRightDerivedAdjunction
    (proEtaleConstantRingDerivedPullback (R l E n) (c.ofIsPullback sq).g)
    (proEtaleConstantRingPushforward (R l E n) (c.ofIsPullback sq).g).rightDerivedFunctor
    (Adjunction.mapDerivedCategoryRightDerivedAdjunction
      (proEtaleConstantRingAdjunction (R l E n) (c.ofIsPullback sq).g))
    (proEtaleConstantRingDerivedPullback (R l E n) g)
    (proEtaleConstantRingDerivedPullback (R l E n) h)
    (proEtaleConstantRingDerivedPullback (R l E n) (pullback.fst c.g g))
    (proEtaleConstantRingPullbackComposition (c.ofIsPullback sq).g g (R l E n) ≪≫
      eqToIso (congrArg (fun a ↦ proEtaleConstantRingDerivedPullback (R l E n) a)
        pullback.condition.symm) ≪≫
      (proEtaleConstantRingPullbackComposition (pullback.fst c.g g) c.g (R l E n)).symm)
    (a.openExchange h (c.ofIsPullback sq).i c.i (pullback.fst c.g g)
      (c.isPullback_i_ofIsPullback sq) n)

/-- The coefficient direct-image comparison is the existing adjunction mate,
with the source and target coefficient systems retained. Source: blueprint
operations proof (2)
(blueprint: def-sp-strict-compactification-comparison-interfaces). -/
abbrev comparisonCoefficientMate (b : Base l E) (o : Operations l E b)
    {X Y : Scheme.{u}} (f : X ⟶ Y) {m n : ℕ} (h : n ≤ m) :=
  (o.geometry f).generic.coefficientMate
    (Scheme.ProEt.topology Y) (B l E Y) (tau l E Y) (b.calculus Y)
    (Scheme.ProEt.topology X)
    (proEtaleSheafInverseImage f (Type (u + 1)))
    (proEtaleSheafDirectImage f (Type (u + 1)))
    (proEtaleSheafAdjunction f (Type (u + 1))) h

/-- Coefficient and tensor coherence of the actual strict-system calculus.
Source: blueprint operations proof (2)
(blueprint: def-sp-strict-compactification-comparison-interfaces). -/
def StrictSystemComparisons (b : Base l E) (o : Operations l E b) : Prop :=
  (∀ T : Scheme.{u},
    ∃ s : SemilinearSections.SemilinearDerivedSectionsData.{u + 1, u, u + 1}
      (Scheme.ProEt.topology T) (B l E T) (tau l E T), s.systems = b.calculus T) ∧
  (∀ (T : Scheme.{u}) (K L : D l E T) {m n : ℕ} (h : n ≤ m),
    SemilinearSections.reduction (Scheme.ProEt.topology T) (B l E T) (tau l E T)
        h ((b.calculus T).scalar h) ((tensor l E b T).obj (K, L)) ≫
          ((b.calculus T).tensorEvaluation n).hom.app (K, L) =
      ((b.calculus T).scalar h).T.map
          (((b.calculus T).tensorEvaluation m).hom.app (K, L)) ≫
        ((b.calculus T).scalarTensor h).hom.app
          ((Ev l E T m).obj K, (Ev l E T m).obj L) ≫
        (comparisonLevelTensor l E b T n).map
          (Prod.mkHom
            (SemilinearSections.reduction (Scheme.ProEt.topology T) (B l E T)
              (tau l E T) h ((b.calculus T).scalar h) K)
            (SemilinearSections.reduction (Scheme.ProEt.topology T) (B l E T)
              (tau l E T) h ((b.calculus T).scalar h) L))) ∧
  (∀ (T : Scheme.{u}) {r m n : ℕ} (h : n ≤ m) (k : m ≤ r)
    (K L : SemilinearSections.D.{u + 1, u, u + 1}
      (Scheme.ProEt.topology T) (B l E T r)),
    ((b.calculus T).scalar h).T.map
        (((b.calculus T).scalarTensor k).hom.app (K, L)) ≫
      ((b.calculus T).scalarTensor h).hom.app
        (((b.calculus T).scalar k).T.obj K, ((b.calculus T).scalar k).T.obj L) ≫
      (comparisonLevelTensor l E b T n).map
        (Prod.mkHom (((b.calculus T).scalarComposition h k).hom.app K)
          (((b.calculus T).scalarComposition h k).hom.app L)) =
    ((b.calculus T).scalarComposition h k).hom.app
        ((comparisonLevelTensor l E b T r).obj (K, L)) ≫
      ((b.calculus T).scalarTensor (h.trans k)).hom.app (K, L)) ∧
  (∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
    {r m n : ℕ} (h : n ≤ m) (k : m ≤ r)
    (Q : SemilinearSections.D.{u + 1, u, u + 1}
      (Scheme.ProEt.topology X) ((o.geometry f).generic.coefficients r)),
    ((b.calculus Y).scalar h).T.map
        ((comparisonCoefficientMate l E b o f k).app Q) ≫
      (comparisonCoefficientMate l E b o f h).app
        (((o.geometry f).generic.target.scalar k).T.obj Q) ≫
      ((o.geometry f).generic.levelPush n).rightDerivedFunctor.map
        (((o.geometry f).generic.target.scalarComposition h k).hom.app Q) =
    ((b.calculus Y).scalarComposition h k).hom.app
        (((o.geometry f).generic.levelPush r).rightDerivedFunctor.obj Q) ≫
      (comparisonCoefficientMate l E b o f (h.trans k)).app Q)

/-- Compatibility with bounded-below injective-resolution derivation.
Source: blueprint operations proof (2); Stacks 05TI, 070J
(blueprint: def-sp-strict-compactification-comparison-interfaces). -/
def StrictPlusComparisons (b : Base l E) (o : Operations l E b)
    [enoughInjectives : ∀ T : Scheme.{u}, EnoughInjectives (S l E T)] : Prop :=
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    ∃ a : SemilinearSections.AdjunctionEvaluation
      (DerivedCategory.Plus.ι (C := S l E Y))
      (DerivedCategory.Plus.ι (C := S l E X))
      (o.geometry f).ordinaryAdjunction.derivedPlus (adjunction l E b (o.geometry f)),
      a.left = (o.geometry f).pull.mapDerivedCategoryPlusCompatibility ∧
      a.right = (o.geometry f).push.rightDerivedFunctorPlusCompatibility

/-- Bounded-below evaluation is pinned by the same ordinary evaluation square
and the canonical comparisons with unbounded derivation.
Source: blueprint operations proof (2)
(blueprint: def-sp-strict-compactification-comparison-interfaces). -/
def StrictPlusEvaluation (b : Base l E) (o : Operations l E b)
    [enoughInjectives : ∀ T : Scheme.{u}, EnoughInjectives (S l E T)]
    [levelEnoughInjectives : ∀ (T : Scheme.{u}) (n : ℕ),
      EnoughInjectives (proEtaleRingModules T (proEtaleConstantRing T (R l E n)))] : Prop :=
  ∃ comparison : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ),
    (o.geometry f).push.rightDerivedFunctorPlus ⋙ (ev l E Y n).mapDerivedCategoryPlus ≅
      (ev l E X n).mapDerivedCategoryPlus ⋙
        (proEtaleConstantRingPushforward (R l E n) f).rightDerivedFunctorPlus,
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (K : DerivedCategory.Plus (S l E X)),
    DerivedCategory.Plus.ι.map ((comparison f n).hom.app K) ≫
        (proEtaleConstantRingPushforward (R l E n) f).rightDerivedFunctorPlusCompatibility.hom.app
          ((ev l E X n).mapDerivedCategoryPlus.obj K) =
      (ev l E Y n).mapDerivedCategoryPlusCompatibility.hom.app
          ((o.geometry f).push.rightDerivedFunctorPlus.obj K) ≫
        (Ev l E Y n).map ((o.geometry f).push.rightDerivedFunctorPlusCompatibility.hom.app K) ≫
        ((o.geometry f).pushEvaluation n).hom.app K.obj ≫
        (proEtaleConstantRingPushforward (R l E n) f).rightDerivedFunctor.map
          ((ev l E X n).mapDerivedCategoryPlusCompatibility.inv.app K)

/-- Fixed-scalar realization at a positive coefficient level, using the published
identity-section equivalence. Source: blueprint operations proof (2)
(blueprint: def-sp-strict-compactification-comparison-interfaces). -/
abbrev comparisonFiniteRealization (b : Base l E) (T : Scheme.{u}) (n : ℕ) :=
  (sfIntrinsicModuleEquivalence T (R l E n)).functor.mapDerivedCategory

/-- The ordinary pullback square in the fixed-scalar realization. Its only
extra factor is the realization unit, so the square fixes the actual scalar
and section action. Source: blueprint operations proof (2)
(blueprint: def-sp-strict-compactification-comparison-interfaces). -/
def comparisonFiniteOrdinaryPull (b : Base l E) {X Y : Scheme.{u}}
    (f : X ⟶ Y) (n : ℕ) :
    (sfIntrinsicModuleEquivalence Y (R l E n)).functor ⋙
        proEtaleConstantRingPullback (R l E n) f ≅
      upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))) f ⋙
        (sfIntrinsicModuleEquivalence X (R l E n)).functor :=
  Functor.isoWhiskerLeft (sfIntrinsicModuleEquivalence Y (R l E n)).functor
      (openSquarePullbackModel (R l E n) f) ≪≫
    (sfIntrinsicModuleEquivalence Y (R l E n)).funInvIdAssoc _

/-- The derived fixed-scalar pullback square, with the published exact-functor
comparison to total left derivation. Source: blueprint operations proof (2)
(blueprint: def-sp-strict-compactification-comparison-interfaces). -/
def comparisonFinitePull (b : Base l E) {X Y : Scheme.{u}}
    (f : X ⟶ Y) (n : ℕ) :
    (upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))) f).leftDerivedFunctor ⋙
        comparisonFiniteRealization l E b X n ≅
      comparisonFiniteRealization l E b Y n ⋙
        proEtaleConstantRingDerivedPullback (R l E n) f :=
  Functor.isoWhiskerRight
      (upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n)))
        f).leftDerivedFunctorIsoMapDerivedCategory
      (comparisonFiniteRealization l E b X n) ≪≫
    (Functor.mapDerivedCategorySquareIso (comparisonFiniteOrdinaryPull l E b f n)).symm

/-- The ordinary open-extension square, determined solely by the realization
unit. Source: blueprint operations proof (2)
(blueprint: def-sp-strict-compactification-comparison-interfaces). -/
def comparisonFiniteOrdinaryOpen (b : Base l E) {U T : Scheme.{u}}
    (j : U ⟶ T) [IsOpenImmersion j] (n : ℕ) :
    openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))) j ⋙
        (sfIntrinsicModuleEquivalence T (R l E n)).functor ≅
      (sfIntrinsicModuleEquivalence U (R l E n)).functor ⋙
        sfIntrinsicExtensionByZero j (R l E n) :=
  ((sfIntrinsicModuleEquivalence U (R l E n)).funInvIdAssoc _).symm

/-- Exact derived open-extension square for the canonical scalar realization.
Source: blueprint operations proof (2)
(blueprint: def-sp-strict-compactification-comparison-interfaces). -/
def comparisonFiniteOpen (b : Base l E) {U T : Scheme.{u}}
    (j : U ⟶ T) [IsOpenImmersion j] (n : ℕ) :
    (openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n)))
        j).mapDerivedCategory ⋙ comparisonFiniteRealization l E b T n ≅
      comparisonFiniteRealization l E b U n ⋙ sfIntrinsicDerivedOpen (R l E n) j := by
  letI := sfIntrinsicExtensionByZero_additive j (R l E n)
  letI := sfIntrinsicExtensionByZero_preservesFiniteLimits j (R l E n)
  letI := sfIntrinsicExtensionByZero_preservesFiniteColimits j (R l E n)
  exact Functor.mapDerivedCategorySquareIso (comparisonFiniteOrdinaryOpen l E b j n)

/-- An adjunction square allowing the fixed-scalar sheaf presentation and the
intrinsic module presentation to have different Hom universes. The unit and
counit equations determine the right-adjoint comparison from the left one.
Source: blueprint operations proof (2), invariance of adjunction mates under
coefficient realization
(blueprint: def-sp-strict-compactification-comparison-interfaces). -/
structure ComparisonAdjunctionCoordinates
    {C₁ : Type c₁} {C₂ : Type c₂} {C₃ : Type c₃} {C₄ : Type c₄}
    [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} C₃] [Category.{v₄} C₄]
    (e : C₁ ⥤ C₃) (d : C₂ ⥤ C₄)
    {L : C₁ ⥤ C₂} {G : C₂ ⥤ C₁} (adj : L ⊣ G)
    {l : C₃ ⥤ C₄} {g : C₄ ⥤ C₃} (level : l ⊣ g) where
  left : L ⋙ d ≅ e ⋙ l
  right : G ⋙ e ≅ d ⋙ g
  unit : ∀ K : C₁,
    e.map (adj.unit.app K) ≫ right.hom.app (L.obj K) ≫
      g.map (left.hom.app K) = level.unit.app (e.obj K)
  counit : ∀ K : C₂,
    l.map (right.hom.app K) ≫ level.counit.app (d.obj K) =
      left.inv.app (G.obj K) ≫ d.map (adj.counit.app K)

/-- Right-adjoint coordinates are pinned by their actual left-adjoint square
and both adjunction equations. There is no free comparison of direct images.
Source: blueprint operations proof (2)
(blueprint: def-sp-strict-compactification-comparison-interfaces). -/
def StrictFiniteCoordinates (b : Base l E) : Type _ :=
  { adjunctions : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ),
    ComparisonAdjunctionCoordinates
      (comparisonFiniteRealization l E b Y n) (comparisonFiniteRealization l E b X n)
      (derivedUpperStarLowerStarAdjunction
        (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))) f)
      (Adjunction.mapDerivedCategoryRightDerivedAdjunction
        (proEtaleConstantRingAdjunction (R l E n) f))
  // ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ),
    (adjunctions f n).left = comparisonFinitePull l E b f n }

/-- Compact-support coordinates are the composite of the normalized open and
proper right-adjoint coordinates. Source: blueprint operations proof (2)
(blueprint: def-sp-strict-compactification-comparison-interfaces). -/
def comparisonFiniteF (b : Base l E) (a : StrictFiniteCoordinates l E b)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) (n : ℕ) :
    rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))) c ⋙
        comparisonFiniteRealization l E b Y n ≅
      comparisonFiniteRealization l E b X n ⋙ finiteF l E b c n :=
  Functor.isoWhiskerLeft
      (openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n)))
        c.i).mapDerivedCategory (a.val c.g n).right ≪≫
    Functor.isoWhiskerRight (comparisonFiniteOpen l E b c.i n) _

/-- The finite exchange is the recorded ambient exchange, and on every specified
etale witness it is the transported etale exchange. Coordinates in this square
are fixed by ordinary sections and adjunction units, not chosen for this arrow.
Source: blueprint operations proof (2); compact-support exchange transport,
lines 21--22 (blueprint: def-sp-strict-compactification-comparison-interfaces). -/
def StrictFiniteExchangeComparisons (b : Base l E) (o : Operations l E b)
    (levels : ComparisonLevels l E b o) (a : StrictFiniteCoordinates l E b) : Prop :=
  (∀ {X' X Y' Y : Scheme.{u}} {h : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] (sq : IsPullback h f' f g) (c : Compactification f) (n : ℕ)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n)))))
    (N : DerivedCategory (Sheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n)))))
    (alpha : (comparisonUpperStar
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))) X).mapDerivedCategory.obj L.obj ≅ N),
    (comparisonFiniteRealization l E b Y' n).map
        (compactExchangeTransportAtWitness (ULift.{u + 1, u} (R l E n)) sq c L N alpha) ≫
      (comparisonFiniteF l E b a (c.ofIsPullback sq) n).hom.app
        ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n)))
          h).leftDerivedFunctor.obj N) ≫
      (finiteF l E b (c.ofIsPullback sq) n).map
        ((comparisonFinitePull l E b h n).hom.app N) =
    (comparisonFinitePull l E b g n).hom.app
        ((rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))) c).obj N) ≫
      (proEtaleConstantRingDerivedPullback (R l E n) g).map
        ((comparisonFiniteF l E b a c n).hom.app N) ≫
      (comparisonLevelExchange l E b o levels sq c n).app
        ((comparisonFiniteRealization l E b X n).obj N))

/-- The published finite projection word with product tensor endpoints made explicit.
Only the currying wrappers are expanded; the actual projection map is retained.
Source: blueprint operations proof (2); def-exchange-projection
(blueprint: def-sp-strict-compactification-comparison-interfaces). -/
def comparisonFiniteProjection (b : Base l E) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (n : ℕ)
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n)))))
    (L : DerivedCategory (Sheaf (Scheme.ProEt.topology Y)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))))) :
    (SheafOfModules.OpenTensorNormalization.finiteTensor.{u}
      (ULift.{u + 1, u} (R l E n)) Y).obj
        ((rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))) c).obj K, L) ⟶
      (rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))) c).obj
          ((SheafOfModules.OpenTensorNormalization.finiteTensor.{u}
            (ULift.{u + 1, u} (R l E n)) X).obj
              (K, (upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n)))
                f).leftDerivedFunctor.obj L)) := by
  unfold SheafOfModules.OpenTensorNormalization.finiteTensor
  exact ((projectionMapOfCompactification
    (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))) c).app K).app L

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

end AlgebraicGeometry.ProEtale.SpTowerShriek
