/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.Strict.Etale.StrictEtaleIsomorphicStageProjectionInterfaces
public import Mathlib.LinearAlgebra.Basis.Defs
import WeilConjectures.AlgebraicGeometry.Strict.Etale.StrictEtaleDerivedQuotientInterchange
import WeilConjectures.AlgebraicGeometry.Strict.Etale.StrictEtaleFiniteFreeOpenFaces
import WeilConjectures.AlgebraicGeometry.Strict.Etale.StrictEtaleFiniteFreeProperFaces
import WeilConjectures.AlgebraicGeometry.Strict.Etale.StrictEtaleFiniteFreeScalarExact
/-! # Finite-free strict etale scalar comparison -/
@[expose] public noncomputable section
set_option autoImplicit false
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
