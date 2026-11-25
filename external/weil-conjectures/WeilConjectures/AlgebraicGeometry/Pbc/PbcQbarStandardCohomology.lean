/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pbc.PbcCohomologySheaves
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralTStructure
public import WeilConjectures.AlgebraicGeometry.Localized.LocalizedTStructure

/-! # Standard cohomology at common finite coefficient stages

This extends the recorded ambient and rational cohomology to the actual Qbar pair
category. Invertibility is required on the scheme, including the empty scheme.

## References

* Bhatt--Scholze, Section 6.8, Propositions 6.8.11 and 6.8.14
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

variable (l : ℕ) [Fact l.Prime] (Ω : Type w) [Field Ω]
  [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω] (X : Scheme.{u}) [IsNoetherian X]
  [hDim : Fact (∃ n : ℕ, topologicalKrullDim X ≤ (n : WithBot ℕ∞))]
  [hInv : Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]

end AlgebraicGeometry.Scheme
