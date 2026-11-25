/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Scalar.ScalarExtensionFunctor
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionDirectImageComparison
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constructible.ProEtaleConstructibleSheaf
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitude
public import WeilConjectures.Compactification.NagataCompactification

public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicExtensionByZero

import all WeilConjectures.AlgebraicGeometry.Finite.Constant.FiniteConstantProjectionFormula
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteLocalizingExceptionalPreservation
import WeilConjectures.AlgebraicGeometry.ProEtale.Direct.ProEtaleDirectImageScalarCocycle
import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenScalarCocycle
import all WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingConstructibleDerivedOrigin
import WeilConjectures.AlgebraicGeometry.Etale.Origin.EtaleOriginScalarProjectionSquare
import WeilConjectures.SixFunctors.Etale.Derived.DirectImageAmplitude
import all WeilConjectures.AlgebraicGeometry.Etale.ProEtale.EtaleProEtaleExceptionalObjectComparison
import WeilConjectures.AlgebraicGeometry.SupportedEtaleTensorOrigin.SupportedEtaleTensorOrigin
import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicTorAmplitudeTransport

/-!
# Compact support and finite coefficient extension

The comparison uses the specified counit mate and the unit-normalized open tensor
comparison. All categories are ordinary uncompleted module derived categories.
-/

@[expose] public noncomputable section

set_option linter.privateModule false
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option linter.unusedVariables false
-- Replaying categorical transport tactics for linting duplicates elaboration work.
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor
  completedAdicDerivedChange directImageScalarComparison reductionOpenScalarIso
  scalarExtensionFunctor_composition
  Etale.derivedTensor Etale.lowerStar Etale.upperStar
  Etale.rightDerivedLowerStarProjectionMap Etale.scalarTensorIso

private theorem bounded_iff_finite_support
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (K : DerivedCategory C) :
    DerivedCategory.TStructure.t.bounded K ↔
      Set.Finite {i : ℤ | ¬ IsZero ((DerivedCategory.homologyFunctor C i).obj K)} := by
  constructor
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    apply (Set.finite_Icc a b).subset
    intro i hi
    exact ⟨le_of_not_gt (fun h ↦ hi ((DerivedCategory.isGE_iff K a).mp ha i h)),
      le_of_not_gt (fun h ↦ hi ((DerivedCategory.isLE_iff K b).mp hb i h))⟩
  · intro h
    obtain ⟨a, ha⟩ := h.bddBelow
    obtain ⟨b, hb⟩ := h.bddAbove
    refine ⟨⟨a, (DerivedCategory.isGE_iff K a).mpr (fun i hi ↦ ?_)⟩,
      ⟨b, (DerivedCategory.isLE_iff K b).mpr (fun i hi ↦ ?_)⟩⟩
    · by_contra hz
      exact (not_lt_of_ge (ha hz)) hi
    · by_contra hz
      exact (not_lt_of_ge (hb hz)) hi

-- Diagnose elaboration without unfolding large derived-functor constructions indefinitely.
private theorem scalarMateRestriction_reflectsIso
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) (Y : Scheme.{u}) :
    (scalarMateRestriction φ Y).mapDerivedCategory.ReflectsIsomorphisms := by
  let r := scalarMateRestriction φ Y
  have : PreservesFiniteLimits r :=
    (Scheme.proEtaleRingRestrictScalars_properties
      (Scheme.proEtaleConstantRingMap (T := Y) φ)).1
  have : PreservesFiniteColimits r :=
    (Scheme.proEtaleRingRestrictScalars_properties
      (Scheme.proEtaleConstantRingMap (T := Y) φ)).2.1
  have : r.ReflectsIsomorphisms :=
    (Scheme.proEtaleRingRestrictScalars_properties
      (Scheme.proEtaleConstantRingMap (T := Y) φ)).2.2
  refine ⟨fun f _ ↦ ?_⟩
  rw [DerivedCategory.isIso_iff]
  intro n
  have : IsIso (r.map ((DerivedCategory.homologyFunctor _ n).map f)) :=
    (NatIso.isIso_map_iff (r.mapDerivedCategoryHomologyFunctorIso n) f).2
      (by rw [Functor.comp_map]; infer_instance)
  exact isIso_of_reflects_iso _ r

-- Keep categorical transport elaboration within a predictable resource bound.
end AlgebraicGeometry.ProEtale
