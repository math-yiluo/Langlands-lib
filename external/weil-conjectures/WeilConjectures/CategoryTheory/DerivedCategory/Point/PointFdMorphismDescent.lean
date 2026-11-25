/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Field.FieldDerivedScalarTower
public import WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import WeilConjectures.CategoryTheory.DerivedCategory.Field.FieldDerivedScalarTower
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import WeilConjectures.CategoryTheory.DerivedCategory.Field.FieldComplexCohomologySplitting
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! # Descent of a morphism between finite coefficient complexes

Source: blueprint order 1509, the common-stage Hom construction for
`lemma-perfect-complexes-geometric-point` (blueprint: lem-weil-point-fd-morphism-descent).
-/

@[expose] public section

universe u v

open CategoryTheory

namespace DerivedCategory

attribute [local irreducible] Module.Basis.baseChange ModuleCat.extendScalarsComp

open scoped TensorProduct

end DerivedCategory
