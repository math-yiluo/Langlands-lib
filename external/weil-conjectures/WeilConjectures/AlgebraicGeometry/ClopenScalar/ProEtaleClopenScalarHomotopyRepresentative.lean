/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ClopenScalar.ProEtaleClopenDerivedScalarData

/-! # The homotopy form of the scalar representative square

Source: Stacks Project, sites-cohomology.tex, Tag 06YY.
(blueprint: lem-pur-clopen-scalar-homotopy-representative)
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false


@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
universe t u
open CategoryTheory CategoryTheory.Limits Opposite
open SheafOfModules.SuccessiveDerivedQuotient
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.ClopenLocalization.modulesAbelian
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.ClopenLocalization.hasDerived
attribute [local irreducible] DerivedCategory.Q Functor.mapDerivedCategory
  Functor.mapDerivedCategoryFactors HasDerivedCategory.standard DerivedCategory.Qh
  DerivedCategory.quotientCompQhIso Functor.mapDerivedCategoryFactorsh
  Functor.mapHomotopyCategoryFactors SheafOfModules.monoidalCategory
namespace AlgebraicGeometry.Scheme.ProEt.ClopenScalar

section QuotientFormulas

variable {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B]

omit [HasDerivedCategory A] [HasDerivedCategory B] in
private theorem homotopyFactors_inv (F : A ⥤ B) [F.Additive]
    (P : CochainComplex A ℤ) :
    (F.mapHomotopyCategoryFactors (.up ℤ)).inv.app P = 𝟙 _ := by
  unfold Functor.mapHomotopyCategoryFactors
  rfl

end QuotientFormulas

attribute [local irreducible] computation

-- The quotient square has several dependent localization and coefficient functor types.
end AlgebraicGeometry.Scheme.ProEt.ClopenScalar
