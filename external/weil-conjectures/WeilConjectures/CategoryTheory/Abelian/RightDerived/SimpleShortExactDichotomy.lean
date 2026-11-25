/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Simple
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Endpoints of a short exact sequence with simple middle object

Source: the ordinary truncation argument in the latest blueprint,
`prop-a1-curve-perverse-simples.proof.md`, paragraph "Every simple object".
(blueprint: lem-a1-simple-short-exact-dichotomy).
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory.Limits

namespace CategoryTheory.ShortComplex

variable {C : Type*} [Category C] [HasZeroMorphisms C]

/-- If the middle term is simple, a short exact sequence has a zero endpoint.
Proof: its first map is either zero or an isomorphism by simplicity. A zero mono
has zero source. If it is an isomorphism, cancellation makes the second map zero,
and a zero epi has zero target.
Source: latest blueprint, `prop-a1-curve-perverse-simples.proof.md`, ordinary
truncation sequence (blueprint: lem-a1-simple-short-exact-dichotomy). -/
theorem ShortExact.isZero_left_or_right {S : ShortComplex C} (hS : S.ShortExact)
    [Simple S.X₂] : IsZero S.X₁ ∨ IsZero S.X₃ := by
  have : Mono S.f := hS.mono_f
  have : Epi S.g := hS.epi_g
  by_cases hf : S.f = 0
  · exact Or.inl (IsZero.of_mono_eq_zero S.f hf)
  · have : IsIso S.f := isIso_of_mono_of_nonzero hf
    apply Or.inr
    apply IsZero.of_epi_eq_zero S.g
    rw [← cancel_epi S.f, S.zero, comp_zero]

end CategoryTheory.ShortComplex
