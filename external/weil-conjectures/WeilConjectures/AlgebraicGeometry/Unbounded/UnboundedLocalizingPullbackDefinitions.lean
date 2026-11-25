/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.CategoryTheory.Monoidal.CommMon_
public import WeilConjectures.CategoryTheory.SixFunctors.LocalizingClosure

/-! # The canonical localizing pullback preservation proposition

Source: blueprint latest, sec-six-functors-basics/sk-prop-proper-base-change-unbounded,
sk-prop-proper-base-change-unbounded-pullback.proof.md, exactness, sums and localizing closures
(blueprint: def-zl-unbounded-localizing-pullback).

These two declarations are moved from
`WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedLocalizingPullback` with their
names, signatures, and bodies unchanged. The canonical shift is constructed from the
existing exact-derived comparison; the proposition records the ambient and restricted
preservation clauses without asserting them. The localizing hull and constant-model
constructibility are the existing imported definitions.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- The canonical shift-commutation of the total derived inverse image `Lg^*`: the one of the
termwise functor `D(g^*)` (Mathlib's `Functor.mapDerivedCategory`), transported along the
canonical isomorphism `CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory`. Exactness of
`Lg^*` is asserted for this shift structure, not for an arbitrary one.
Source: blueprint main-20261015, inverse image on the localizing categories
(blueprint: def-zl-unbounded-localizing-pullback). -/
@[instance_reducible]
def unboundedLocalizingPullbackCommShift
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {Y' Y : Scheme.{u}} (g : Y' ⟶ Y) :
    (CondensedRing.upperStar Λ g).leftDerivedFunctor.CommShift ℤ :=
  Functor.CommShift.ofIso (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ g).symm ℤ

attribute [local instance] unboundedLocalizingPullbackCommShift

/-- The clauses of inverse-image preservation, including its restriction along the full
inclusions. `Lg^*` carries its canonical shift-commutation
`unboundedLocalizingPullbackCommShift`; the restriction is Mathlib's `ObjectProperty.lift` of
`Lg^*` along the full inclusions, with its inherited shift-commutation, and the triangulations
on the restricted categories are the inherited ones.
Source: blueprint main-20261015, inverse image on the localizing categories
(blueprint: def-zl-unbounded-localizing-pullback). -/
structure UnboundedLocalizingPullback
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {Y' Y : Scheme.{u}} (g : Y' ⟶ Y) : Prop where
  exact : (CondensedRing.upperStar Λ g).leftDerivedFunctor.IsTriangulated
  sums : ∀ I : Type (u + 2),
    PreservesColimitsOfShape (Discrete I) (CondensedRing.upperStar Λ g).leftDerivedFunctor
  constructible : ∀ K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)),
    (constantModelBoundedConstructible Λ Y K ∧ DerivedCategory.finiteTorAmplitude _ K) →
    constantModelBoundedConstructible Λ Y'
        ((CondensedRing.upperStar Λ g).leftDerivedFunctor.obj K) ∧
      DerivedCategory.finiteTorAmplitude _
        ((CondensedRing.upperStar Λ g).leftDerivedFunctor.obj K)
  localizing : ∀ K : (localizingClosureProEtale Λ Y).FullSubcategory,
    localizingClosureProEtale Λ Y'
      (((localizingClosureProEtale Λ Y).ι ⋙ (CondensedRing.upperStar Λ g).leftDerivedFunctor).obj K)
  [sourceTriangulated : (localizingClosureProEtale Λ Y).IsTriangulated]
  [targetTriangulated : (localizingClosureProEtale Λ Y').IsTriangulated]
  restrictionExact : ((localizingClosureProEtale Λ Y').lift
    ((localizingClosureProEtale Λ Y).ι ⋙ (CondensedRing.upperStar Λ g).leftDerivedFunctor)
    localizing).IsTriangulated
  restrictionSums : ∀ I : Type (u + 2), PreservesColimitsOfShape (Discrete I)
    ((localizingClosureProEtale Λ Y').lift
      ((localizingClosureProEtale Λ Y).ι ⋙ (CondensedRing.upperStar Λ g).leftDerivedFunctor)
      localizing)

end AlgebraicGeometry.ProEtale
