/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Completed.CompletedCompactSupportExchange
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralUniformCoefficient
public import WeilConjectures.AlgebraicGeometry.Strict.Tower.StrictTowerOperationsSupplement
public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.CompletedDirectImageLimits
public import WeilConjectures.AlgebraicGeometry.Iso.IsoSectionwiseInverseImage
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
public import WeilConjectures.CategoryTheory.Ringed.RingedStrictTowerHomotopyLimitOfUniverses
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
public import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleAmbientRingedExchange
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback

/-!
# Reindexing completed modules and strict reductions by scheme isomorphisms

The ordinary pullbacks are the tensor presentations of inverse-image
reindexing, with the canonical completed coefficient identifications. The predicates
below expand the clauses of this one statement; they introduce no new coefficient,
completion, reduction, or direct-image construction. All tower derived categories
are derived categories of actual strict diagrams, with positive level n+1 indexed by n.

## References

* Stacks Tags 09A5, 0A07, 07A4, 0G7E, 099N and 07A7
* Stacks Tag 07A7, using the completed coefficient composition equations
* Stacks Tag 07A7 on the ringed diagram site
* Stacks Tag 07A7, with the coherent completed coefficient maps
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option linter.privateModule false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local irreducible] completedAdicChangeData completedReductionCoefficient
attribute [local irreducible] proEtaleRingModulePullback
attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor
attribute [local irreducible] CochainComplex.IsKFlatIndependentCoefficients
attribute [local instance 2000] reductionModulesHasDerivedCategory reductionTowerHasDerivedCategory

variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)

/-- Whisker a transformation between composites, with the composite tower functors
written explicitly. -/
def purWhiskerCompositeMap
    {J C D D' E : Type*} [Category J] [Category C] [Category D] [Category D'] [Category E]
    (F : C ⥤ D) (G : D ⥤ E) (F' : C ⥤ D') (G' : D' ⥤ E)
    (a : F ⋙ G ⟶ F' ⋙ G') :
    (Functor.whiskeringRight J C D).obj F ⋙ (Functor.whiskeringRight J D E).obj G ⟶
      (Functor.whiskeringRight J C D').obj F' ⋙ (Functor.whiskeringRight J D' E).obj G' :=
  (Functor.whiskeringRight J C E).map a

/-- The canonical completed-coefficient specialization of the ringed square. -/
def purReindexingRingedSquare {X' X Y' Y : Scheme.{t}}
    {v : X' ⟶ X} {p' : X' ⟶ Y'} {p : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare v p' p g) : StrictTowerRingedSquare sq where
  RY := d.completedRing Y
  RX := d.completedRing X
  RY' := d.completedRing Y'
  RX' := d.completedRing X'
  cf := d.integralRingIso p
  cg := d.integralRingIso g
  cg' := d.integralRingIso v
  cf' := d.integralRingIso p'
  coherent := d.integral_coherent sq

/-- The ordinary module mate of the specified, section-normalized pullback square. -/
def purReindexingModuleMate {X' X Y' Y : Scheme.{t}}
    {v : X' ⟶ X} {p' : X' ⟶ Y'} {p : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare v p' p g) :
    proEtaleRingModuleDirectImage p (d.completedRing Y) (d.completedRing X)
        (d.integralRingIso p) ⋙ proEtaleRingModulePullback g (d.completedRing Y)
        (d.completedRing Y') (d.integralRingIso g) ⟶
      proEtaleRingModulePullback v (d.completedRing X)
        (d.completedRing X') (d.integralRingIso v) ⋙
        proEtaleRingModuleDirectImage p' (d.completedRing Y') (d.completedRing X')
          (d.integralRingIso p') :=
  (mateEquiv
    (proEtaleRingModuleAdjunction p (d.completedRing Y) (d.completedRing X)
      (d.integralRingIso p))
    (proEtaleRingModuleAdjunction p' (d.completedRing Y') (d.completedRing X')
      (d.integralRingIso p'))
    (TwoSquare.mk _ _ _ _ (purReindexingRingedSquare d sq).exchangeModuleSquare.hom))

/-- The actual ordinary strict-diagram mate, including every index arrow. -/
def purReindexingTowerModuleMate {X' X Y' Y : Scheme.{t}}
    {v : X' ⟶ X} {p' : X' ⟶ Y'} {p : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare v p' p g) :
    d.towerModulePush p ⋙ d.towerModulePull g ⟶
      d.towerModulePull v ⋙ d.towerModulePush p' :=
  purWhiskerCompositeMap (J := ℕᵒᵖ) _ _ _ _ (purReindexingModuleMate d sq)

/-- The specified ordinary completed-ring derived direct-image mate. -/
def purReindexingDerivedMate {X' X Y' Y : Scheme.{t}}
    {v : X' ⟶ X} {p' : X' ⟶ Y'} {p : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare v p' p g) :
    d.push p ⋙ d.pull g ⟶ d.pull v ⋙ d.push p' :=
  proEtaleAmbientRingedExchange sq
    (d.completedRing X) (d.completedRing Y) (d.completedRing X') (d.completedRing Y')
    (d.integralRingIso p) (d.integralRingIso g) (d.integralRingIso v)
    (d.integralRingIso p') (d.integral_coherent sq)

/- Exact reindexing, its reverse, its normalized limit comparison, and its strict
reduction tensor normalization. The ordinary tensor presentation is canonically
inverse image with action a.x = c inverse(a).x; no completeness restriction is imposed
on the equivalences or on the inverse-limit comparison.
Source: Stacks Tags 09A5, 0A07, 03EL and 099N. -/

/-- A literal clause of PurCompletedReindexingAt. -/
def PurCompletedReindexingAtLimit {T' T : Scheme.{t}} (u : T' ⟶ T) [IsIso u] : Prop :=
  (∃ beta : completedTowerLimit T (d.completedRing T) ⋙
      proEtaleRingModulePullback u (d.completedRing T)
        (d.completedRing T') (d.integralRingIso u) ≅
      d.towerModulePull u ⋙ completedTowerLimit T' (d.completedRing T'),
    (∀ (C : d.towers T) (n : ℕᵒᵖ),
      beta.hom.app C ≫ limit.π ((d.towerModulePull u).obj C) n =
        (proEtaleRingModulePullback u (d.completedRing T)
        (d.completedRing T') (d.integralRingIso u)).map (limit.π C n)) ∧
    ∃ b : completedRlim T (d.completedRing T) ⋙ d.pull u ≅
      d.towerPull u ⋙ completedRlim T' (d.completedRing T'),
    (∀ I : CochainComplex (d.towers T) ℤ, I.IsKInjective →
      (d.pull u).map ((completedTowerLimit T (d.completedRing T)).rightDerivedFunctorUnitQ I) ≫
        b.hom.app (DerivedCategory.Q.obj I) ≫
        (completedRlim T' (d.completedRing T')).map
          ((d.towerModulePull u).mapDerivedCategoryFactors.hom.app I) =
      (proEtaleRingModulePullback u (d.completedRing T)
        (d.completedRing T') (d.integralRingIso u)).mapDerivedCategoryFactors.hom.app
          (((completedTowerLimit T (d.completedRing T)).mapHomologicalComplex (.up ℤ)).obj I) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex beta.hom (.up ℤ)).app I) ≫
        (completedTowerLimit T' (d.completedRing T')).rightDerivedFunctorUnitQ
          (((d.towerModulePull u).mapHomologicalComplex (.up ℤ)).obj I)) ∧
    (∀ K : d.derived T, d.TowerComplete T K →
      ∃ e : (d.completedPull u).obj K ≅ (d.pull u).obj K,
        e.inv = d.ordinaryToCompleted u K ∧
        e.hom ≫ (d.pull u).map (d.completionUnit T K) =
          b.inv.app ((completedReductionTower T d).obj K)))

/- Section and K-injective normalizations of both specified direct-image mates.
The first equation is restriction along the canonical fibre-product square after
inverse-image units. Since g is an isomorphism, its base-changed tests cover all tests.
The last equations identify the derived mates on actual K-injective complexes,
including strict tower complexes, rather than merely asserting they are invertible.
Source: Stacks Tags 07A7, 08BJ and 0FND. -/
/-- A literal clause of PurCompletedReindexingSquare. -/
def PurCompletedReindexingSquareDerived {X' X Y' Y : Scheme.{t}}
    {v : X' ⟶ X} {p' : X' ⟶ Y'} {p : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare v p' p g) : Prop :=
  IsIso (purReindexingDerivedMate d sq)

/-- A literal clause of PurCompletedReindexingSquare. -/
def PurCompletedReindexingSquareDerivedTowers {X' X Y' Y : Scheme.{t}}
    {v : X' ⟶ X} {p' : X' ⟶ Y'} {p : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare v p' p g) : Prop :=
  IsIso (purReindexingRingedSquare d sq).exchangeTowerMate

/-- A literal clause of PurCompletedReindexingSquare. -/
def PurCompletedReindexingSquareDerivedUnits {X' X Y' Y : Scheme.{t}}
    {v : X' ⟶ X} {p' : X' ⟶ Y'} {p : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare v p' p g) : Prop :=
  (∀ I : CochainComplex (reductionModules X (d.completedRing X)) ℤ, I.IsKInjective →
    (d.pull g).map
        ((proEtaleRingModuleDirectImage p (d.completedRing Y) (d.completedRing X)
          (d.integralRingIso p)).rightDerivedFunctorUnitQ I) ≫
      (purReindexingDerivedMate d sq).app (DerivedCategory.Q.obj I) ≫
      (d.push p').map ((proEtaleRingModulePullback v (d.completedRing X)
        (d.completedRing X') (d.integralRingIso v)).mapDerivedCategoryFactors.hom.app I) =
    (proEtaleRingModulePullback g (d.completedRing Y)
        (d.completedRing Y') (d.integralRingIso g)).mapDerivedCategoryFactors.hom.app
        (((proEtaleRingModuleDirectImage p (d.completedRing Y) (d.completedRing X)
          (d.integralRingIso p)).mapHomologicalComplex (.up ℤ)).obj I) ≫
      DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex (purReindexingModuleMate d sq) (.up ℤ)).app I) ≫
      (proEtaleRingModuleDirectImage p' (d.completedRing Y') (d.completedRing X')
        (d.integralRingIso p')).rightDerivedFunctorUnitQ
          (((proEtaleRingModulePullback v (d.completedRing X)
        (d.completedRing X') (d.integralRingIso v)).mapHomologicalComplex (.up ℤ)).obj I))

/-- A literal clause of PurCompletedReindexingSquare. -/
def PurCompletedReindexingSquareDerivedTowerUnits {X' X Y' Y : Scheme.{t}}
    {v : X' ⟶ X} {p' : X' ⟶ Y'} {p : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare v p' p g) : Prop :=
  (∀ I : CochainComplex (d.towers X) ℤ, I.IsKInjective →
    (d.towerPull g).map ((d.towerModulePush p).rightDerivedFunctorUnitQ I) ≫
      (purReindexingRingedSquare d sq).exchangeTowerMate.app (DerivedCategory.Q.obj I) ≫
      (d.towerPush p').map ((d.towerModulePull v).mapDerivedCategoryFactors.hom.app I) =
    (d.towerModulePull g).mapDerivedCategoryFactors.hom.app
        (((d.towerModulePush p).mapHomologicalComplex (.up ℤ)).obj I) ≫
      DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex (purReindexingTowerModuleMate d sq) (.up ℤ)).app I) ≫
      (d.towerModulePush p').rightDerivedFunctorUnitQ
        (((d.towerModulePull v).mapHomologicalComplex (.up ℤ)).obj I))

end AlgebraicGeometry.Scheme
