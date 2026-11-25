/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Strict.Etale.StrictEtaleFiniteFreeScalarCoordinates
public import WeilConjectures.AlgebraicGeometry.Strict.Etale.StrictEtaleIsomorphicStageProjectionInterfaces
public import Mathlib.CategoryTheory.Adjunction.Mates
import all WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportScalarAction
import WeilConjectures.AlgebraicGeometry.Strict.Etale.StrictEtaleFiniteFreeScalarExact
import all WeilConjectures.CategoryTheory.Ringed.Finite.RingedFiniteFreeHomBaseChangeCoordinates

/-! # Basis columns of the proper coefficient mate

Source: Zheng, Construction 5.15 and Lemma 5.16.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option genSizeOf false
set_option genCtorIdx false
set_option synthInstance.maxSize 4096
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor SheafOfModules
open scoped ChangeOfRings
universe a b c d av bv cv dv

universe u
namespace AlgebraicGeometry
attribute [local instance 5000] strictEtaleSystemDerived strictEtaleLevelDerived

end AlgebraicGeometry
