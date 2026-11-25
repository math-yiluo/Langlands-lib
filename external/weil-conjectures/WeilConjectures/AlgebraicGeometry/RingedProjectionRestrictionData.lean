/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
public import WeilConjectures.Algebra.Homology.BoundedAboveFlatSheafKFlat
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.AlgebraicGeometry.ProEtaleOperationsCanonicalAdjunction
public import WeilConjectures.AlgebraicGeometry.RingedTopoiCanonicalTensorPullback
public import WeilConjectures.AlgebraicGeometry.StrictPerfectCoefficientPackage
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMap
public import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
public import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.Monoidal.Dualizable
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutions
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Canonical localization comparisons for the projection mate

Source: Stacks Project, Cohomology on Sites, Tags 08FI, 0FN5, 07A4 and 0B56;
Modules on Sites, Tag 04J0 (auxiliary; not a blueprint node).

All model functors below carry natural representative comparisons. Ordinary operations
are Mathlib's module pullback and pushforward for the specified ring map. Tensor
comparisons are normalized on pure tensors and signed total complexes; derived
adjunctions are normalized by the ordinary counit on K-injectives. No operation or
projection arrow is selected from an unconstrained existence statement.

## Main definitions

* `ProjectionRestriction.Operation`: the canonical module and derived operations.
* `ProjectionRestriction.TensorModel`: derived tensor normalized on resolving pairs.
* `ProjectionRestriction.Local`: canonical slice comparisons and their normalizations.

The assembly theorem `ringedProjectionRestriction` is in
`Sheaf.Paper.RingedProjectionRestriction`. This module contains its unchanged data
interfaces so the construction lemmas can be imported without a cycle.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option backward.isDefEq.respectTransparency true
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.ProjectionRestriction

variable {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
  [EssentiallySmall.{u + 1} C] [EssentiallySmall.{u + 1} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}

/-- Modules with the original coefficient universe.
Source: Stacks 04IX (auxiliary; not a blueprint node). -/
abbrev Mod (R : Sheaf J CommRingCat.{u + 1}) :=
  SheafOfModules.{u + 1} ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)

/-- The standard localization size for these module categories.
Source: Stacks 05RU (auxiliary; not a blueprint node). -/
instance derived (R : Sheaf J CommRingCat.{u + 1}) : HasDerivedCategory (Mod R) :=
  HasDerivedCategory.standard _

/-- Standard localization on the slice site.
Source: Stacks 05RU (auxiliary; not a blueprint node). -/
instance derivedOver (R : Sheaf J CommRingCat.{u + 1}) (V : C) :
    HasDerivedCategory (Mod (R.over V)) := HasDerivedCategory.standard _

/-- The same standard localization for the raw slice-ring presentation.
Source: Stacks 05RU (auxiliary; not a blueprint node). -/
instance derivedOverModules (R : Sheaf J RingCat.{u + 1}) (V : C) :
    HasDerivedCategory (SheafOfModules.{u + 1} (R.over V)) := HasDerivedCategory.standard _

/-- Proof data for the actual module operations associated to a continuous ringed site map.
The only ring map is the displayed coefficient map. The adjunction, exact pullback and
K-injective direct image are then fixed constructions.
Source: Stacks 04J0, 0735, 07A5 (auxiliary; not a blueprint node). -/
structure Operation (F : C ⥤ D) (R : Sheaf J CommRingCat.{u + 1})
    (S : Sheaf K CommRingCat.{u + 1}) where
  [continuous : F.IsContinuous J K]
  coefficient : ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) ⟶
    (F.sheafPushforwardContinuous RingCat.{u + 1} J K).obj
      ((sheafCompose K (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S)
  [rightAdjoint : (SheafOfModules.pushforward.{u + 1} coefficient).IsRightAdjoint]
  [pullbackAdditive : (SheafOfModules.pullback.{u + 1} coefficient).Additive]
  [pushforwardAdditive : (SheafOfModules.pushforward.{u + 1} coefficient).Additive]
  [pullbackLimits : PreservesFiniteLimits (SheafOfModules.pullback.{u + 1} coefficient)]
  [pullbackColimits : PreservesFiniteColimits (SheafOfModules.pullback.{u + 1} coefficient)]
  [kInjectives : Abelian.HasKInjectiveResolutions (Mod S)]

attribute [instance] Operation.rightAdjoint Operation.pullbackAdditive
  Operation.pushforwardAdditive Operation.pullbackLimits Operation.pullbackColimits

namespace Operation

variable {F : C ⥤ D} {R : Sheaf J CommRingCat.{u + 1}}
  {S : Sheaf K CommRingCat.{u + 1}} (o : Operation F R S)

end Operation

namespace Operation
end Operation

end AlgebraicGeometry.Scheme.ProjectionRestriction

namespace AlgebraicGeometry.Scheme.ProjectionRestriction
variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (R_Y : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
  (R_X : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
  (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R_Y ≅ R_X)

end AlgebraicGeometry.Scheme.ProjectionRestriction
