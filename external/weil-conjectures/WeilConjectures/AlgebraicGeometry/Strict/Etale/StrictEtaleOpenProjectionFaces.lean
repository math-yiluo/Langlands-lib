/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Strict.Etale.StrictEtaleIsomorphicStageProjectionInterfaces
import WeilConjectures.AlgebraicGeometry.Strict.Etale.StrictEtaleLevelInverseConstruction
import WeilConjectures.AlgebraicGeometry.Strict.Etale.StrictEtaleOpenInverseEvaluation
import WeilConjectures.AlgebraicGeometry.Strict.Etale.StrictEtaleLevelInverseQuotient
import WeilConjectures.CategoryTheory.SixFunctors.MateIsoAlongEquivalences
import Mathlib.CategoryTheory.Adjunction.Opposites
import WeilConjectures.CategoryTheory.DerivedCategory.AdjunctionMateTranspose
import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.CategoryTheory.Derived.DerivedMateComparison

/-! # Normalized geometric projection faces

Source: Zheng, Construction 5.15 and Lemma 5.22.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option genInjectivity false
set_option genSizeOfSpec false
set_option genSizeOf false
set_option genCtorIdx false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor SheafOfModules
namespace AlgebraicGeometry
attribute [local instance 5000] strictEtaleSystemDerived strictEtaleLevelDerived

end AlgebraicGeometry
