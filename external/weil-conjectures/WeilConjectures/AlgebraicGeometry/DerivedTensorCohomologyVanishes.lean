/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.Algebra.Homology.KFlat
public import Mathlib.Algebra.Homology.Single

/-! # Vanishing of derived tensor cohomology on a scheme

Source: Stacks Project, Cohomology on Sites, Tags 06YS and 06YU;
Derived Categories of Schemes, Tag 08EA
(blueprint: def-pc-derived-tensor-cohomology-vanishes).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry

set_option synthInstance.maxSize 256 in
/-- Vanishing of `H^i(E ⊗ᴸ F)` is expressed by a K-flat representative `P` of `E`
whose total tensor with `F` in degree zero has zero cohomology in degree `i`.
The representative is required to exist: this predicate cannot hold vacuously.
K-flat resolutions exist (Tag 06YS), and different K-flat representatives compute
isomorphic derived tensor products (Tag 06YU). Thus existential choice of a
representative gives exactly vanishing of the derived tensor cohomology sheaf.
Source: Stacks Project, Tags 06YS, 06YU and 08EA
(blueprint: def-pc-derived-tensor-cohomology-vanishes). -/
def schemeDerivedTensorCohomologyVanishes (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (E : schemeDerivedCategory X)
    (F : SheafOfModules.{u} (moduleRings X.toRingedSpace)) (i : ℤ) : Prop :=
  letI := SheafOfModules.monoidalCategory X.sheaf
  ∃ P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ,
    CochainComplex.IsKFlatTensor (R := X.sheaf) P ∧
      Nonempty (DerivedCategory.Q.obj P ≅ E) ∧
      IsZero ((CochainComplex.mapBifunctor P
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj F)
        (curriedTensor _)).homology i)

end AlgebraicGeometry
