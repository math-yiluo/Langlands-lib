/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassReduction
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-! # Integral line-bundle classes and geometric pullback

Source: blueprint, sec-smooth-purity/sk-prop-sp-tower-geometric,
classes proof (2), and the integral extension argument in steps 1--3 of
lem-sp-tower-chern-pullback (blueprint: def-sp-tower-integral-pullback-data).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale.SpTowerClasses

/-- Exact inverse image of entire abelian towers, by componentwise sheaf inverse image.
Source: the system-topos construction (blueprint: def-sp-tower-integral-pullback-data). -/
def abPull {X Y : Scheme.{u}} (f : X ⟶ Y) : Ab Y ⥤ Ab X :=
  (Functor.whiskeringRight ℕᵒᵖ (DiagonalAb Y) (DiagonalAb X)).obj
    (upperStar AddCommGrpCat.{u + 1} f)

/-- Componentwise inverse image preserves addition.
Source: blueprint classes proof (2)
(blueprint: def-sp-tower-integral-pullback-data). -/
instance abPull_additive {X Y : Scheme.{u}} (f : X ⟶ Y) : (abPull f).Additive := by
  unfold abPull
  infer_instance

/-- Componentwise inverse image preserves finite limits.
Source: blueprint classes proof (2)
(blueprint: def-sp-tower-integral-pullback-data). -/
instance abPull_limits {X Y : Scheme.{u}} (f : X ⟶ Y) :
    PreservesFiniteLimits (abPull f) := by
  unfold abPull
  exact ⟨fun _ _ _ ↦ inferInstance⟩

/-- Componentwise inverse image preserves finite colimits.
Source: blueprint classes proof (2)
(blueprint: def-sp-tower-integral-pullback-data). -/
instance abPull_colimits {X Y : Scheme.{u}} (f : X ⟶ Y) :
    PreservesFiniteColimits (abPull f) := by
  unfold abPull
  exact ⟨fun _ _ _ ↦ inferInstance⟩

/-- Pullback of full units along the projection of a base-changed chart.
Source: integral extension gluing (blueprint: def-sp-tower-integral-pullback-data). -/
def unitsDirect {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Scheme.proEtaleUnitsSheaf Y ⟶
      (lowerStar AddCommGrpCat.{u + 1} f).obj (Scheme.proEtaleUnitsSheaf X) :=
  ⟨{ app := fun U ↦ AddCommGrpCat.ofHom
        { toFun := fun x ↦ ULift.up (Additive.ofMul
            (Units.map (pullback.fst U.unop.hom f).appTop.hom.toMonoidHom x.down.toMul))
          map_zero' := by
            apply ULift.ext
            exact (Units.map _).map_one
          map_add' := fun x y ↦ by
            apply ULift.ext
            exact (Units.map _).map_mul x.down.toMul y.down.toMul }
     naturality := by
      intro U V a
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro x
      apply ULift.ext
      apply Additive.toMul.injective
      apply Units.ext
      change (pullback.fst V.unop.hom f).appTop
          (a.unop.left.appTop x.down.toMul.val) =
        ((Scheme.proEtaleBaseChange f).map a.unop).left.appTop
          ((pullback.fst U.unop.hom f).appTop x.down.toMul.val)
      have h : ((Scheme.proEtaleBaseChange f).map a.unop).left ≫
          pullback.fst U.unop.hom f = pullback.fst V.unop.hom f ≫ a.unop.left :=
        pullback.lift_fst _ _ _
      exact congrArg (fun k ↦ k.appTop.hom x.down.toMul.val) h.symm }⟩

/-- Constant-integer comparison on towers, normalized by constant sections.
Source: inverse image of constants (blueprint: def-sp-tower-integral-pullback-data). -/
def integerPull {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (abPull f).obj (integers Y) ⟶ integers X :=
  { app := fun _ ↦ ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv
      ((constantSheaf (Scheme.ProEt.topology Y) AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)))
      ((constantSheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).symm
      (Scheme.proEtaleConstantDirectImageMap f AddCommGrpCat.{u + 1}
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)))
    naturality := fun _ _ _ ↦ by
      change (upperStar AddCommGrpCat.{u + 1} f).map (𝟙 _) ≫ _ = _ ≫ 𝟙 _
      dsimp only [integers, units, constant, Functor.const_obj_obj]
      rw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id] }

/-- Full-units comparison on constant towers, with no invertibility assertion.
Source: integral extension gluing (blueprint: def-sp-tower-integral-pullback-data). -/
def unitsPull {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (abPull f).obj (units Y) ⟶ units X :=
  { app := fun _ ↦ ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv
      (Scheme.proEtaleUnitsSheaf Y) (Scheme.proEtaleUnitsSheaf X)).symm (unitsDirect f)
    naturality := fun _ _ _ ↦ by
      change (upperStar AddCommGrpCat.{u + 1} f).map (𝟙 _) ≫ _ = _ ≫ 𝟙 _
      dsimp only [integers, units, constant, Functor.const_obj_obj]
      rw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id] }

/-- Derived constant-integer comparison, including the canonical single comparison.
Source: exact localization (blueprint: def-sp-tower-integral-pullback-data). -/
def integerDerivedPull {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (abPull f).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor (Ab Y) 0).obj (integers Y)) ⟶
      (DerivedCategory.singleFunctor (Ab X) 0).obj (integers X) :=
  ((abPull f).mapDerivedCategorySingleFunctor 0).hom.app (integers Y) ≫
    (DerivedCategory.singleFunctor (Ab X) 0).map (integerPull f)

/-- Derived units comparison, including the canonical shift by one.
Source: exact localization (blueprint: def-sp-tower-integral-pullback-data). -/
def unitsDerivedPull {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (abPull f).mapDerivedCategory.obj
        (((DerivedCategory.singleFunctor (Ab Y) 0).obj (units Y))⟦(1 : ℤ)⟧) ⟶
      ((DerivedCategory.singleFunctor (Ab X) 0).obj (units X))⟦(1 : ℤ)⟧ :=
  ((abPull f).mapDerivedCategory.commShiftIso (1 : ℤ)).hom.app _ ≫
    (((abPull f).mapDerivedCategorySingleFunctor 0).hom.app (units Y))⟦(1 : ℤ)⟧' ≫
    ((DerivedCategory.singleFunctor (Ab X) 0).map (unitsPull f))⟦(1 : ℤ)⟧'

open CategoryTheory.Abelian

section PullbackNormalization

attribute [local instance 100000] abDerived

attribute [local irreducible] Functor.mapDerivedCategory mapSingleArrow lineBundleEtaleClass

/-- The canonical comparison between constant towers and pointwise inverse image.
Source: blueprint classes proof (2)
(blueprint: def-sp-tower-integral-pullback-data). -/
def towerIntegral_constantPullIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    upperStar AddCommGrpCat.{u + 1} f ⋙ constant X ≅ constant Y ⋙ abPull f :=
  Functor.compConstIso ℕᵒᵖ (upperStar AddCommGrpCat.{u + 1} f)

/-- The inverse-image map of integer sheaves, adjoint to constant sections.
Source: blueprint classes proof (2)
(blueprint: def-sp-tower-integral-pullback-data). -/
def towerIntegral_integerSheafPull {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (upperStar AddCommGrpCat.{u + 1} f).obj
        ((constantSheaf (Scheme.ProEt.topology Y) AddCommGrpCat.{u + 1}).obj
          (AddCommGrpCat.of (ULift.{u + 1} ℤ))) ⟶
      (constantSheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)) :=
  ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv _ _).symm
    (Scheme.proEtaleConstantDirectImageMap f AddCommGrpCat.{u + 1}
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)))

/-- The inverse-image map of full units, adjoint to chartwise unit pullback.
Source: blueprint classes proof (2)
(blueprint: def-sp-tower-integral-pullback-data). -/
def towerIntegral_unitsSheafPull {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (upperStar AddCommGrpCat.{u + 1} f).obj (Scheme.proEtaleUnitsSheaf Y) ⟶
      Scheme.proEtaleUnitsSheaf X :=
  ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv _ _).symm
    (unitsDirect f)

/-- The integer tower endpoint is the constant image of its ordinary sheaf endpoint.
Source: blueprint classes proof (2)
(blueprint: def-sp-tower-integral-pullback-data). -/
theorem towerIntegral_integerPull_iso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    integerPull f = (towerIntegral_constantPullIso f).inv.app
        ((constantSheaf (Scheme.ProEt.topology Y) AddCommGrpCat.{u + 1}).obj
          (AddCommGrpCat.of (ULift.{u + 1} ℤ))) ≫
      (constant X).map (towerIntegral_integerSheafPull f) := by
  apply NatTrans.ext
  funext n
  change towerIntegral_integerSheafPull f = 𝟙 _ ≫ towerIntegral_integerSheafPull f
  rw [Category.id_comp]

/-- The units tower endpoint is the constant image of its ordinary sheaf endpoint.
Source: blueprint classes proof (2)
(blueprint: def-sp-tower-integral-pullback-data). -/
theorem towerIntegral_unitsPull_iso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (towerIntegral_constantPullIso f).hom.app (Scheme.proEtaleUnitsSheaf Y) ≫ unitsPull f =
      (constant X).map (towerIntegral_unitsSheafPull f) := by
  apply NatTrans.ext
  funext n
  change 𝟙 _ ≫ towerIntegral_unitsSheafPull f = towerIntegral_unitsSheafPull f
  rw [Category.id_comp]

/-- Transposing the chosen units inverse image recovers the chartwise units map.
Source: blueprint classes proof (2)
(blueprint: def-sp-tower-integral-pullback-data). -/
theorem towerIntegral_unitsSheafPull_transpose {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv
      (Scheme.proEtaleUnitsSheaf Y) (Scheme.proEtaleUnitsSheaf X))
        (towerIntegral_unitsSheafPull f) = unitsDirect f := by
  exact Equiv.apply_symm_apply _ (unitsDirect f)

/-- The direct units map pulls back along the fibre-product projection.
Source: blueprint classes proof (2)
(blueprint: def-sp-tower-integral-pullback-data). -/
theorem towerIntegral_unitsDirect_apply {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : Y.ProEtᵒᵖ) (x : (Scheme.proEtaleUnitsSheaf Y).obj.obj U) :
    (unitsDirect f).hom.app U x =
      ULift.up (Additive.ofMul
        (Units.map (pullback.fst U.unop.hom f).appTop.hom.toMonoidHom x.down.toMul)) := by
  rfl

/-- The ordinary units endpoint has the required normalized adjoint on each chart.
Source: blueprint classes proof (2)
(blueprint: def-sp-tower-integral-pullback-data). -/
theorem towerIntegral_unitsPull_adjoint {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : Y.ProEtᵒᵖ) (x : (Scheme.proEtaleUnitsSheaf Y).obj.obj U) :
    (((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv _ _)
        (towerIntegral_unitsSheafPull f)).hom.app U x =
      ULift.up (Additive.ofMul
        (Units.map (pullback.fst U.unop.hom f).appTop.hom.toMonoidHom x.down.toMul)) := by
  exact (congrArg
    (fun k : Scheme.proEtaleUnitsSheaf Y ⟶
      (lowerStar AddCommGrpCat.{u + 1} f).obj (Scheme.proEtaleUnitsSheaf X) ↦
        k.hom.app U x) (towerIntegral_unitsSheafPull_transpose f)).trans
    (towerIntegral_unitsDirect_apply f U x)

end PullbackNormalization

end AlgebraicGeometry.ProEtale.SpTowerClasses
