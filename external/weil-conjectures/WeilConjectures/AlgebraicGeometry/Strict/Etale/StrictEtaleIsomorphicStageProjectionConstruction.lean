/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Strict.Etale.StrictEtaleIsomorphicStageProjectionInterfaces
import WeilConjectures.AlgebraicGeometry.Strict.Etale.StrictEtaleDerivedQuotientInterchange
import WeilConjectures.AlgebraicGeometry.Strict.Etale.StrictEtaleOpenProjectionFaces
import WeilConjectures.AlgebraicGeometry.Strict.Etale.StrictEtaleProperProjectionFaces

/-!
# Compact-support projection from strict étale transports

Source: Zheng, Construction 5.15 and Lemma 5.22
(blueprint: lem-pur-strict-etale-isomorphic-stage-projection).

This is the geometric mate assembly after exact coefficient transports have been
constructed.  It leaves coefficient transport construction to a separate node.
-/

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
