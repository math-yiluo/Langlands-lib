/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.PrincipalTorsorComparisons.PrincipalTorsorSignTypes
/-! Independent comparison result for the principal torsor sign calculation.

## References

* Stacks Tags 03AJ, 0A45, 06XR
-/
@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite HomologicalComplex
namespace AlgebraicGeometry.Etale
/-- The open adjunction and the closed-support resolution comparison admit the normalization
on every cocycle used in the sign calculation. -/
theorem principalTorsorNormalizedComparison :
    ∃ C : PrincipalTorsorComparisons.{u}, C.Normalized := by sorry
end AlgebraicGeometry.Etale
