/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import Mathlib.Algebra.Homology.Additive
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper

/-!
# Colimits and geometric stalks

Source: Stacks Project, Tags 03PN and 04K1; blueprint node
`definition-torsion-sheaves--3` (blueprint: definition-torsion-sheaves--3).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- (blueprint: definition-torsion-sheaves--3) Let `T` be a scheme and `s` a geometric
point of `T`. The geometric stalk of sheaves of abelian groups on the small etale
site of `T` commutes with arbitrary colimits. In each degree the same holds for
complexes of abelian sheaves, whose colimits are computed termwise.

The stalk functor is left adjoint to the skyscraper sheaf functor, so it
preserves colimits (Mathlib `Point.skyscraperSheafAdjunction`). To obtain colimits
in the source sheaf category at the indicated universe, factor the forgetful
functor from integer modules through abelian groups: its first factor preserves
all colimits, and its second factor preserves filtered colimits. Mathlib's affine
etale sheafification instances then supply colimits of sheaves. Finally,
`HomologicalComplex.preservesColimitsOfShape_of_eval`, through the instance in
`HomologicalComplexAbelian`, gives preservation degreewise for each diagram shape.
Source: Stacks Project, Tags 03PN and 04K1; Mathlib
`CategoryTheory/Sites/Point/Skyscraper.lean` and
`Algebra/Homology/HomologicalComplexAbelian.lean`. -/
theorem geometricStalk_preservesColimits
    {T : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (s : Spec (.of Ω) ⟶ T) :
    PreservesColimits
      ((pointSmallEtale s).sheafFiber (A := ModuleCat.{u} ℤ)) ∧
    PreservesColimits
      (((pointSmallEtale s).sheafFiber (A := ModuleCat.{u} ℤ)).mapHomologicalComplex
        (ComplexShape.up ℤ)) := by
  refine ⟨inferInstance, ⟨?_⟩⟩
  intro J _
  have : PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget (ModuleCat.{u} ℤ)) :=
    Limits.comp_preservesFilteredColimits
      (forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u})
      (CategoryTheory.forget AddCommGrpCat.{u})
  infer_instance

end AlgebraicGeometry.Scheme
