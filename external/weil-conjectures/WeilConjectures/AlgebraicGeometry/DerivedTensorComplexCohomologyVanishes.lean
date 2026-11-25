/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedTensorCohomologyVanishes

/-! # Vanishing of derived tensor cohomology for two derived objects

Source: Stacks Project, Cohomology on Sites, Tags 06YS and 06YU;
Derived Categories of Schemes, Tag 09M4, spectral sequence in the proof
(blueprint: def-pc-derived-tensor-complex-cohomology-vanishes).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry

set_option synthInstance.maxSize 256 in
/-- Vanishing of `H^i(E ⊗ᴸ L)` for two objects of `D(𝒪_X)`: choose a K-flat representative
`K` of `E` and a complex `N` representing `L`, and require the degree `i` cohomology of
`Tot(K ⊗ N)` to be zero. Representatives must exist, so this predicate is not vacuous.
K-flat replacement (Tag 06YS), essential surjectivity of `Q`, and independence of
representatives (Tag 06YU) identify this with derived tensor cohomology vanishing.
It extends `schemeDerivedTensorCohomologyVanishes`, whose second argument is a module
placed in degree zero; it does not replace that existing predicate.
Source: Stacks Project, Tags 06YS and 06YU; Tag 09M4, spectral sequence in the proof
(blueprint: def-pc-derived-tensor-complex-cohomology-vanishes). -/
def schemeDerivedTensorComplexCohomologyVanishes (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (E L : schemeDerivedCategory X) (i : ℤ) : Prop :=
  letI := SheafOfModules.monoidalCategory X.sheaf
  ∃ K N : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ,
    CochainComplex.IsKFlatTensor (R := X.sheaf) K ∧
      Nonempty (DerivedCategory.Q.obj K ≅ E) ∧
      Nonempty (DerivedCategory.Q.obj N ≅ L) ∧
      IsZero ((CochainComplex.mapBifunctor K N (curriedTensor _)).homology i)

end AlgebraicGeometry
