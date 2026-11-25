/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.FourCornersSupplement
public import WeilConjectures.AlgebraicGeometry.Completed.CompletedRlimFunctor
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCompletion
public import WeilConjectures.AlgebraicGeometry.Completed.CompletedReductionUnit
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-!
# Exact interface for strict completed-coefficient towers

Source: blueprint proper base change, completed pullback; Stacks Tag 099N
(blueprint: def-weil-pbc-exact-pullback-interface).

## Main definitions

- `AlgebraicGeometry.Scheme.AdicCoefficientDatum.constantRlimAdjunction`:
  the derived constant-tower and inverse-limit adjunction.
- `AlgebraicGeometry.Scheme.AdicCoefficientDatum.completionUnit`:
  the adjunction unit followed by the normalized quotient augmentation.
- `AlgebraicGeometry.Scheme.AdicCoefficientDatum.towerPull`:
  exact termwise pullback and its compatibility with constant towers.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)

/-- The ordinary constant strict tower functor.
Source: blueprint completed pullback (blueprint: def-weil-pbc-exact-pullback-interface). -/
abbrev AdicCoefficientDatum.constantTower (T : Scheme.{t}) :
    reductionModules T (d.completedRing T) ⥤ d.towers T := Functor.const ℕᵒᵖ

/-- Exact constant towers on the derived category.
Source: blueprint completed pullback (blueprint: def-weil-pbc-exact-pullback-interface). -/
abbrev AdicCoefficientDatum.derivedConstantTower (T : Scheme.{t}) :=
  (d.constantTower T).mapDerivedCategory

/-- Constant towers are left adjoint to the chosen total right derived inverse limit.
Source: blueprint completed pullback; Stacks 079P
(blueprint: def-weil-pbc-exact-pullback-interface). -/
def AdicCoefficientDatum.constantRlimAdjunction (T : Scheme.{t}) :
    d.derivedConstantTower T ⊣ completedRlim T (d.completedRing T) :=
  (constLimAdj :
    d.constantTower T ⊣ completedTowerLimit T (d.completedRing T)
  ).mapDerivedCategoryRightDerivedAdjunction

/-- Reuse the published derived quotient unit, including its K-flat normalization.
Source: blueprint completed pullback; Stacks 06YY and 099N
(blueprint: def-weil-pbc-exact-pullback-interface). -/
abbrev completedReductionAugmentation (T : Scheme.{t}) :
    d.derivedConstantTower T ⟶ completedReductionTower T d :=
  completedReductionTowerUnit d T

/-- The canonical completion unit, formed by the constant-tower adjunction and quotient map.
Source: blueprint completed pullback (blueprint: def-weil-pbc-exact-pullback-interface). -/
def AdicCoefficientDatum.completionUnit (T : Scheme.{t}) (K : d.derived T) :
    K ⟶ (completedRlim T (d.completedRing T)).obj
      ((completedReductionTower T d).obj K) :=
  (d.constantRlimAdjunction T).unit.app K ≫
    (completedRlim T (d.completedRing T)).map ((completedReductionAugmentation d T).app K)

/-- Quotient-tower completeness is invertibility of the specified canonical completion unit.
This is the completeness condition in the completed base-change construction.
Source: blueprint completed base-change map, input paragraph and canonical quotient unit
(blueprint: def-weil-pbc-exact-pullback-interface). -/
def AdicCoefficientDatum.TowerComplete (T : Scheme.{t}) (K : d.derived T) : Prop :=
  IsIso (d.completionUnit T K)

/-- Apply actual module pullback to every level and transition of a strict tower.
Source: blueprint completed pullback (blueprint: def-weil-pbc-exact-pullback-interface). -/
abbrev AdicCoefficientDatum.towerModulePull {U V : Scheme.{t}} (f : U ⟶ V) :
    d.towers V ⥤ d.towers U :=
  (Functor.whiskeringRight ℕᵒᵖ _ _).obj
    (proEtaleRingModulePullback f (d.completedRing V) (d.completedRing U) (d.integralRingIso f))

/-- Tower pullback is exact: the canonical profinite coefficient map is invertible and
module inverse image is exact; exactness of strict towers is evaluated levelwise.
Source: blueprint completed pullback (blueprint: def-weil-pbc-exact-pullback-interface).
Proof: evaluation commutes with this whiskering functor. Use exactness of ordinary
ringed pullback at every level and the pointwise kernels and cokernels of towers. -/
theorem AdicCoefficientDatum.towerModulePull_exact {U V : Scheme.{t}} (f : U ⟶ V) :
    PreservesFiniteLimits (d.towerModulePull f) ∧
      PreservesFiniteColimits (d.towerModulePull f) := by
  unfold AdicCoefficientDatum.towerModulePull
  constructor
  · exact ⟨fun J _ _ ↦ inferInstance⟩
  · exact ⟨fun J _ _ ↦ inferInstance⟩

/-- Exact tower pullback preserves finite limits.
Source: blueprint completed pullback (blueprint: def-weil-pbc-exact-pullback-interface). -/
instance AdicCoefficientDatum.towerModulePull_finiteLimits {U V : Scheme.{t}} (f : U ⟶ V) :
    PreservesFiniteLimits (d.towerModulePull f) := (d.towerModulePull_exact f).1
/-- Exact tower pullback preserves finite colimits.
Source: blueprint completed pullback (blueprint: def-weil-pbc-exact-pullback-interface). -/
instance AdicCoefficientDatum.towerModulePull_finiteColimits {U V : Scheme.{t}} (f : U ⟶ V) :
    PreservesFiniteColimits (d.towerModulePull f) := (d.towerModulePull_exact f).2

/-- Termwise pullback of strict towers is additive, evaluated at every level.
Source: blueprint completed pullback (blueprint: def-weil-pbc-exact-pullback-interface). -/
instance AdicCoefficientDatum.towerModulePull_additive {U V : Scheme.{t}} (f : U ⟶ V) :
    (d.towerModulePull f).Additive := inferInstance

/-- The total left derived tower pullback, here computed by the exact termwise functor.
Source: blueprint completed pullback (blueprint: def-weil-pbc-exact-pullback-interface). -/
abbrev AdicCoefficientDatum.towerPull {U V : Scheme.{t}} (f : U ⟶ V) :=
  (d.towerModulePull f).mapDerivedCategory

/-- Constant towers commute with actual ordinary pullback, with identity components.
Source: blueprint direct image and limits (blueprint: def-weil-pbc-exact-pullback-interface). -/
def AdicCoefficientDatum.constantPullbackIso {U V : Scheme.{t}} (f : U ⟶ V) :
    d.constantTower V ⋙ d.towerModulePull f ≅
      proEtaleRingModulePullback f (d.completedRing V) (d.completedRing U)
        (d.integralRingIso f) ⋙ d.constantTower U :=
  NatIso.ofComponents
    (fun M ↦ NatIso.ofComponents
      (fun n ↦ Iso.refl
        (((d.towerModulePull f).obj ((d.constantTower V).obj M)).obj n))
      (fun _ ↦ by
        ext n
        simp [AdicCoefficientDatum.constantTower, AdicCoefficientDatum.towerModulePull]))
    (fun _ ↦ by
      ext n
      simp [AdicCoefficientDatum.constantTower, AdicCoefficientDatum.towerModulePull])

/-- The exact derived constant/pullback comparison, induced from identity components.
Source: blueprint direct image and limits (blueprint: def-weil-pbc-exact-pullback-interface). -/
def AdicCoefficientDatum.derivedConstantPullbackIso {U V : Scheme.{t}} (f : U ⟶ V) :
    d.derivedConstantTower V ⋙ d.towerPull f ≅ d.pull f ⋙ d.derivedConstantTower U :=
  Functor.mapDerivedCategoryCompIso (d.constantTower V) (d.towerModulePull f) ≪≫
    Functor.mapDerivedCategoryNatIso (d.constantPullbackIso f) ≪≫
      (Functor.mapDerivedCategoryCompIso
        (proEtaleRingModulePullback f (d.completedRing V) (d.completedRing U)
          (d.integralRingIso f)) (d.constantTower U)).symm

end AlgebraicGeometry.Scheme
