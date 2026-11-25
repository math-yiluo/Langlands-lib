/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerP1.TowerP1CoefficientCoordinates
public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassFinite

/-! # Ordinary coefficient categories with one ring presentation

Source: diagonal-tower trace (1), finite Kummer classes and exact comparison.
(blueprint: def-sfb-finite-ordinary-coefficient-model).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option cleanup.letToHave false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option linter.auxLemma false in
attribute [local instance 100000] AlgebraicGeometry.Etale.DerivedCategoryModule._proof_1
  AlgebraicGeometry.Etale.DerivedCategoryModule._proof_2
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale.DiagonalTrace
open SpTowerClasses

/-- Etale modules using the ring parent of the specified commutative ring.
Source: ordinary coefficient convention
(blueprint: def-sfb-finite-ordinary-coefficient-model). -/
abbrev OrdinaryEtaleModules (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :=
  Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)

/-- Pro-etale modules with the same ring presentation as ordinary etale modules.
Source: exact coefficient comparison
(blueprint: def-sfb-finite-ordinary-coefficient-model). -/
abbrev OrdinaryProEtaleModules (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :=
  Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)

/-- The existing ordinary localization, with its module category stated in the
common ring presentation. Source: ordinary derived coefficients
(blueprint: def-sfb-finite-ordinary-coefficient-model). -/
@[instance_reducible]
def finiteOrdinaryDerived (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :
    HasDerivedCategory.{u + 1} (OrdinaryEtaleModules A T) :=
  Etale.ordinaryFiniteDerivedCategoryInstance A T

attribute [local instance 100001] finiteOrdinaryDerived

/-- Ext exists in the cached ordinary localization.
Source: the chosen ordinary localization
(blueprint: def-sfb-finite-ordinary-coefficient-model). -/
theorem finiteOrdinaryExt (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :
    CategoryTheory.HasExt.{u + 1} (OrdinaryEtaleModules A T) :=
  CategoryTheory.hasExt_of_hasDerivedCategory _

/-- Exact comparison formed before specializing the commutative coefficient ring.
Source: the actual etale/pro-etale comparison functor
(blueprint: def-sfb-finite-ordinary-coefficient-model). -/
def finiteOrdinaryComparison (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :
    OrdinaryEtaleModules A T ⥤ OrdinaryProEtaleModules A T :=
  comparisonUpperStar (ModuleCat.{u + 1} A) T

/-- Exactness inherited from the actual comparison functor.
Source: exact site comparison (blueprint: def-sfb-finite-ordinary-coefficient-model). -/
instance finiteOrdinaryComparisonAdditive (A : Type (u + 1)) [CommRing A]
    (T : Scheme.{u}) : (finiteOrdinaryComparison A T).Additive := by
  unfold finiteOrdinaryComparison
  infer_instance

/-- Exactness inherited from the actual comparison functor.
Source: exact site comparison (blueprint: def-sfb-finite-ordinary-coefficient-model). -/
instance finiteOrdinaryComparisonLimits (A : Type (u + 1)) [CommRing A]
    (T : Scheme.{u}) : PreservesFiniteLimits (finiteOrdinaryComparison A T) := by
  unfold finiteOrdinaryComparison
  infer_instance

/-- Exactness inherited from the actual comparison functor.
Source: exact site comparison (blueprint: def-sfb-finite-ordinary-coefficient-model). -/
instance finiteOrdinaryComparisonColimits (A : Type (u + 1)) [CommRing A]
    (T : Scheme.{u}) : PreservesFiniteColimits (finiteOrdinaryComparison A T) := by
  unfold finiteOrdinaryComparison
  infer_instance

/-- Forgetting formed with the same coefficient-ring parent.
Source: underlying additive sheaves
(blueprint: def-sfb-finite-ordinary-coefficient-model). -/
def finiteOrdinaryForget (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :
    OrdinaryProEtaleModules A T ⥤ DiagonalAb T :=
  sheafCompose (Scheme.ProEt.topology T)
    (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (n : ℕ) [Finite (SpTowerShriek.R l E n)] (T : Scheme.{u})
attribute [local irreducible] Padic Padic.coefficientExtensionIntegers

/-- The existing realization, cached with its ordinary ring presentation before
forming derived functors. Source: intrinsic realization of constant coefficients
(blueprint: def-sfb-finite-ordinary-coefficient-model). -/
def finiteOrdinaryRealization :
    OrdinaryProEtaleModules (FiniteRing l E n) T ⥤
      Scheme.reductionModules T (SpTowerShriek.B l E T n) :=
  SpTowerP1.realization l E n T

/-- The existing intrinsic localization in the category of the realization.
Source: the canonical localization of reduction modules
(blueprint: def-sfb-finite-ordinary-coefficient-model). -/
@[instance_reducible]
def finiteOrdinaryIntrinsicDerived :
    HasDerivedCategory.{u + 2} (Scheme.reductionModules T (SpTowerShriek.B l E T n)) :=
  Scheme.reductionModulesHasDerivedCategory T (SpTowerShriek.B l E T n)

/-- Exactness inherited from the given intrinsic realization.
Source: exact intrinsic realization (blueprint: def-sfb-finite-ordinary-coefficient-model). -/
instance finiteOrdinaryRealizationAdditive :
    (finiteOrdinaryRealization l E n T).Additive := by
  unfold finiteOrdinaryRealization
  infer_instance

/-- Exactness inherited from the given intrinsic realization.
Source: exact intrinsic realization (blueprint: def-sfb-finite-ordinary-coefficient-model). -/
instance finiteOrdinaryRealizationLimits :
    PreservesFiniteLimits (finiteOrdinaryRealization l E n T) := by
  unfold finiteOrdinaryRealization
  infer_instance

/-- Exactness inherited from the given intrinsic realization.
Source: exact intrinsic realization (blueprint: def-sfb-finite-ordinary-coefficient-model). -/
instance finiteOrdinaryRealizationColimits :
    PreservesFiniteColimits (finiteOrdinaryRealization l E n T) := by
  unfold finiteOrdinaryRealization
  infer_instance

/-- The given unit isomorphism in the cached ordinary presentation.
Source: the supplied coefficient coordinates
(blueprint: def-sfb-finite-ordinary-coefficient-model). -/
def finiteOrdinaryUnitCoordinate
    {hT : IsUnit ((l ^ (n + 1) : ℕ) : Γ(T, ⊤))}
    (c : SpTowerP1.CoefficientCoordinates l E n T hT) :
    (finiteOrdinaryRealization l E n T).obj
        ((finiteOrdinaryComparison (FiniteRing l E n) T).obj
          (Etale.ordinaryFiniteConstant (FiniteRing l E n) T)) ≅
      (SpTowerShriek.ev l E T n).obj (coefficient T (Arings l E T)) := c.unit

/-- The given line isomorphism in the cached ordinary presentation.
Source: the supplied coefficient coordinates
(blueprint: def-sfb-finite-ordinary-coefficient-model). -/
def finiteOrdinaryLineCoordinate
    {hT : IsUnit ((l ^ (n + 1) : ℕ) : Γ(T, ⊤))}
    (c : SpTowerP1.CoefficientCoordinates l E n T hT) :
    (finiteOrdinaryRealization l E n T).obj
        ((finiteOrdinaryComparison (FiniteRing l E n) T).obj
          (Scheme.finiteEtaleTateLine T (l ^ (n + 1)) (FiniteRing l E n)
            (ULift.ext (coefficient_annihilates l E n)))) ≅ finiteLine l E T n := c.line

attribute [local instance 100000] CategoryTheory.Abelian.toPreadditive

/-- The actual common Hom type after successive coefficient transports.
Source: exact comparison, realization and scalar forgetting
(blueprint: def-sfb-finite-ordinary-coefficient-model). -/
def FiniteOrdinaryScalarArrow
    (M N : OrdinaryEtaleModules (FiniteRing l E n) T) :=
  (DerivedCategory.singleFunctor (DiagonalAb T) 0).obj
      ((finiteForget l E T n).obj ((finiteOrdinaryRealization l E n T).obj
        ((finiteOrdinaryComparison (FiniteRing l E n) T).obj M))) ⟶
    ((DerivedCategory.singleFunctor (DiagonalAb T) 0).obj
      ((finiteForget l E T n).obj ((finiteOrdinaryRealization l E n T).obj
        ((finiteOrdinaryComparison (FiniteRing l E n) T).obj N))))⟦(2 : ℤ)⟧

end AlgebraicGeometry.ProEtale.DiagonalTrace
