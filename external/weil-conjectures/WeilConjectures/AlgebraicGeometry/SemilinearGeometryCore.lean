/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.SemilinearDerivedCalculus

/-! # Ordinary geometric operations on semilinear systems

Source: Zheng Construction 4.1 and Lemma 4.10; Stacks 079P and 07A4
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe c v r c₂ v₂ k

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory
open scoped ChangeOfRings

namespace WeilConjectures.SemilinearSections

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [ambientSmall : EssentiallySmall.{max c v r} C]
  (B : ℕ → Sheaf J CommRingCat.{max c v r})
  (τ : ∀ n : ℕ, B (n + 1) ⟶ B n)

section Geometry

variable (A : Data.{c, v, r} J B τ)
  {C' : Type c} [Category.{v} C'] [EssentiallySmall.{max c v r} C']
  (J' : GrothendieckTopology C')
  (uInv : Sheaf J (Type (max c v r)) ⥤ Sheaf J' (Type (max c v r)))
  (uPush : Sheaf J' (Type (max c v r)) ⥤ Sheaf J (Type (max c v r)))
  (adjSet : uInv ⊣ uPush)

/-- The geometric operations on actual semilinear system categories.
Coefficient inverse images retain the dependency's algebraic operation equations.
Both direct images are total right derived functors of the specified ordinary
right adjoints; none is an arbitrary functor between parameter categories.
Source: Zheng 4.1 and 4.10; Stacks 079P, 07A4
(auxiliary; not a blueprint node). -/
structure GeometryBase where
  /-- The inverse-image coefficient sheaves C_n. -/
  coefficients : ℕ → Sheaf J' CommRingCat.{max c v r}
  /-- Their inverse-image transitions. -/
  coefficientTransition : ∀ n : ℕ, coefficients (n + 1) ⟶ coefficients n
  /-- Algebraic inverse image, with actual ring/module operations and underlying sheaves. -/
  inverseImage : ∀ n : ℕ, SheafOfModules.AlgebraicInverseImage uInv (B n) (coefficients n)
  /-- The transitions are u-inverse-image of the supplied tau maps. -/
  coefficient_compatibility : ∀ n : ℕ,
    uInv.map ((sheafCompose J (CategoryTheory.forget CommRingCat.{max c v r})).map (τ n)) ≫
        (inverseImage n).ringUnderlying.hom =
      (inverseImage (n + 1)).ringUnderlying.hom ≫
        (sheafCompose J' (CategoryTheory.forget CommRingCat.{max c v r})).map
          (coefficientTransition n)
  /-- The ordinary-derived calculus for that actual inverse-image tower. -/
  target : Data.{c, v, r} J' coefficients coefficientTransition
  /-- Levelwise exact inverse image. -/
  [levelAdditive : ∀ n : ℕ, (inverseImage n).modules.Additive]
  /-- Left exactness of inverse image of modules. -/
  [levelLimits : ∀ n : ℕ, PreservesFiniteLimits (inverseImage n).modules]
  /-- Right exactness of inverse image of modules. -/
  [levelColimits : ∀ n : ℕ, PreservesFiniteColimits (inverseImage n).modules]
  /-- Ordinary direct image at each coefficient level. -/
  levelPush : ∀ n : ℕ, Mod.{c, v, max c v r} J' (coefficients n) ⥤ Mod.{c, v, max c v r} J (B n)
  /-- Its ordinary adjunction. -/
  levelAdjunction : ∀ n : ℕ, (inverseImage n).modules ⊣ levelPush n
  /-- The underlying set-sheaf direct image is the given uPush. -/
  levelPushUnderlying : ∀ n : ℕ,
    levelPush n ⋙ underlying.{c, v, r} J (B n) ≅
      underlying.{c, v, r} J' (coefficients n) ⋙ uPush
  /-- The module adjunction is normalized by the original topos unit. -/
  level_unit_underlying : ∀ (n : ℕ) (M : Mod.{c, v, max c v r} J (B n)),
    (underlying.{c, v, r} J (B n)).map ((levelAdjunction n).unit.app M) ≫
        (levelPushUnderlying n).hom.app ((inverseImage n).modules.obj M) ≫
        uPush.map ((inverseImage n).moduleUnderlying.hom.app M) =
      adjSet.unit.app ((underlying.{c, v, r} J (B n)).obj M)
  /-- Additivity of direct image. -/
  [levelPushAdditive : ∀ n : ℕ, (levelPush n).Additive]
  /-- K-injectives for each target coefficient category. -/
  [levelKInjective : ∀ n : ℕ,
    Abelian.HasKInjectiveResolutions (Mod.{c, v, max c v r} J' (coefficients n))]
  /-- Ordinary inverse image on systems. -/
  pull : Systems.{c, v, max c v r} J B τ ⥤ Systems.{c, v, max c v r} J' coefficients
    coefficientTransition
  /-- It is the levelwise inverse image, on modules and maps. -/
  ordinaryPullEvaluation : ∀ n : ℕ,
    pull ⋙ evaluation.{c, v, max c v r} J' coefficients coefficientTransition n ≅
      evaluation.{c, v, max c v r} J B τ n ⋙ (inverseImage n).modules
  /-- Additivity and exactness on systems. -/
  [pullAdditive : pull.Additive]
  /-- Inverse image preserves finite limits. -/
  [pullLimits : PreservesFiniteLimits pull]
  /-- Inverse image preserves finite colimits. -/
  [pullColimits : PreservesFiniteColimits pull]
  /-- The ordinary system right adjoint. -/
  push : Systems.{c, v, max c v r} J' coefficients coefficientTransition ⥤ Systems.{c, v, max c v
    r} J B τ
  /-- The system adjunction before deriving. -/
  ordinaryAdjunction : pull ⊣ push
  /-- Additivity of system direct image. -/
  [pushAdditive : push.Additive]
  /-- Simultaneous K-injective resolutions on the actual system category. -/
  [systemKInjective : Abelian.HasKInjectiveResolutions
    (Systems.{c, v, max c v r} J' coefficients coefficientTransition)]
  /-- V adjoint to G, where G is the total right derived system pushforward. -/
  adjunction : pull.mapDerivedCategory ⊣ push.rightDerivedFunctor
end Geometry
end WeilConjectures.SemilinearSections
