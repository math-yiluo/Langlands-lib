/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleTower
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedPullbackComposition

/-!
# The four finite-coefficient corners

Source: blueprint, proper base change, four corners; Stacks Project Tags 07A7 and 099M
(blueprint: def-weil-pbc-four-corners).

## Main definitions

- `AlgebraicGeometry.Scheme.AdicCoefficientDatum.fourCorners`:
  the recorded construction or statement of this node.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct ChangeOfRings

namespace AlgebraicGeometry.Scheme

attribute [instance] proEtaleRingRestrictScalars_preservesFiniteLimits
  proEtaleRingRestrictScalars_preservesFiniteColimits

variable {T : Scheme.{u}} {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (a : R ⟶ S)

/-- Ordinary scalar extension, with objects and maps fixed by the tensor construction.
Source: Stacks Tag 06YY (blueprint: def-weil-pbc-four-corners). -/
noncomputable def proEtaleRingExtension : proEtaleRingModules T R ⥤ proEtaleRingModules T S :=
  reductionChange T a

/-- The fixed scalar extension is additive. Source: Stacks Tag 06YY
(blueprint: def-weil-pbc-four-corners). -/
noncomputable instance proEtaleRingExtension_additive : (proEtaleRingExtension a).Additive :=
  reductionChangeAdditive T a

/-- Reuse the published tensor-unit normalized ordinary scalar adjunction.
Source: Stacks 03D3, 06YY (blueprint: def-weil-pbc-four-corners). -/
noncomputable abbrev proEtaleRingExtensionAdjunction :
    proEtaleRingExtension a ⊣ proEtaleRingRestrictScalars a := pbcScalarAdjunction a

end AlgebraicGeometry.Scheme
