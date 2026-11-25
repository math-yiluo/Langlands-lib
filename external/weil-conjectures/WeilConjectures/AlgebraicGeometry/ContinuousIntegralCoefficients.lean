/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficientData
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory

/-! # Bounded constructible integral coefficients

The coefficient rings, maps and exact sequences are reexported from
`ContinuousIntegralCoefficientData`. This module adds their bounded constructible category.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]

/-- The bounded constructible category with integral continuous coefficients.
Source: Bhatt--Scholze, Section 6.8
(auxiliary; not a blueprint node). -/
noncomputable abbrev integralConstructible (X : Scheme.{u}) :=
  ProEtale.BoundedConstructible (condensedRingObj (integralCoeff ℓ E) X)

end AlgebraicGeometry.ProEtale.CondensedRing
