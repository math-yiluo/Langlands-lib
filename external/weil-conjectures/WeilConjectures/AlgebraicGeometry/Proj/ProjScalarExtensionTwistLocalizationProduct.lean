/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Proj.ProjScalarExtensionTwistData

/-! A localization identity used in the local fraction calculation.

## References

* Stacks Project, Tag 01N2
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Proj

/-- Multiplication by a denominator turns a displayed localization fraction into its numerator. -/
theorem localization_mk_mul_denominator
    {R : Type u} [CommRing R] (P : Ideal R) [P.IsPrime]
    (a b : R) (hb : b ∉ P) :
    Localization.mk (a * b) (⟨b, hb⟩ : P.primeCompl) = Localization.mk a 1 := by
  apply (Localization.mk_eq_mk_iff).2
  rw [Localization.r_eq_r', Localization.r']
  refine ⟨1, ?_⟩
  simp [mul_comm]

end AlgebraicGeometry.Proj
