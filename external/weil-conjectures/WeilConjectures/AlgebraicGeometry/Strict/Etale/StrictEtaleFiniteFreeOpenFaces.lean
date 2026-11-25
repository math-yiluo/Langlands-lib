/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.Strict.Etale.StrictEtaleIsomorphicStageProjectionInterfaces
import all WeilConjectures.AlgebraicGeometry.Strict.Etale.StrictEtaleOpenProjectionFaces
import WeilConjectures.Algebra.Homology.InverseImageScalarRestriction.InverseImageScalarRestrictionComparison
import all WeilConjectures.AlgebraicGeometry.Strict.Etale.StrictEtaleFiniteOrdinaryInverseTransport
import WeilConjectures.AlgebraicGeometry.Strict.Etale.StrictEtaleOpenOrdinaryCalculation
import WeilConjectures.AlgebraicGeometry.Strict.Etale.StrictEtaleOpenInverseEvaluation
import WeilConjectures.AlgebraicGeometry.Strict.Etale.StrictEtaleLevelInverseQuotient
import WeilConjectures.CategoryTheory.Derived.DerivedMateComparison
import WeilConjectures.CategoryTheory.Derived.DerivedSquareIndependentUniverses
import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageExact
/-! Finite-free open projection face for strict étale systems. -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor SheafOfModules
namespace AlgebraicGeometry
attribute [local instance 5000] strictEtaleSystemDerived strictEtaleLevelDerived
end AlgebraicGeometry
