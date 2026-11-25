/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ClopenScalar.ProEtaleClopenDerivedScalarData
import WeilConjectures.AlgebraicGeometry.ClopenScalar.ProEtaleClopenScalarComparisonDescent
import WeilConjectures.AlgebraicGeometry.ClopenScalar.ProEtaleClopenDerivedScalarModels
import WeilConjectures.AlgebraicGeometry.ClopenScalar.ProEtaleClopenDerivedScalarUnits
import WeilConjectures.AlgebraicGeometry.ClopenScalar.ProEtaleClopenScalarComparisonCoherence

/-! # Normalized scalar witnesses for arbitrary coefficient presentations

Source: Stacks Project, sites-cohomology.tex, Tags 06YY and 0D6D.
(blueprint: lem-pur-clopen-arbitrary-scalar-normalized-witnesses)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
universe t u w
open CategoryTheory CategoryTheory.Limits Opposite
open SheafOfModules.SuccessiveDerivedQuotient
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.ClopenLocalization.modulesAbelian
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.ClopenLocalization.hasDerived
attribute [local irreducible] DerivedCategory.Q Functor.mapDerivedCategory
  Functor.mapDerivedCategoryFactors HasDerivedCategory.standard
  SheafOfModules.monoidalCategory
namespace AlgebraicGeometry.Scheme.ProEt.ClopenScalar

end AlgebraicGeometry.Scheme.ProEt.ClopenScalar
