/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import WeilConjectures.AlgebraicGeometry.SchemeDescentDataCategory

/-!
# Blueprint statements

lem-galois-descent.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Required definitions for lem-galois-descent. -/
protected abbrev FiniteEtaleDescentData {Y Y' : Scheme.{u}} (g : Y' ⟶ Y) :
    Type (u + 1) :=
  ObjectProperty.FullSubcategory fun A : Over.DescentDataCategory g ↦
    IsFinite A.V.hom ∧ Etale A.V.hom

end AlgebraicGeometry
