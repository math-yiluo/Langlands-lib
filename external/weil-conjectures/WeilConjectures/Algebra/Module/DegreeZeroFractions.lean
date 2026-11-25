/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Module.LocalizedModule.Basic

/-!
# Equal-degree fractions in a localized graded module

Source: Stacks Project, Algebra, Section 00JM, homogeneous localization at a prime
(blueprint: def-sc-degree-zero-module-fractions).
-/

@[expose] public section

universe uF vF wF

namespace LocalizedModule

/-- The subset of the ordinary localization represented by a homogeneous numerator and
homogeneous denominator of equal degree. The ordinary localization quotient supplies precisely
the equivalence relation `∃ t ∈ T, t • (h' • y - h • y') = 0`.
Source: Stacks Project, Algebra, Section 00JM, definition of `M_(p)`.
(blueprint: def-sc-degree-zero-module-fractions) -/
def degreeZeroFractions {R : Type uF} [CommRing R] {M : Type vF} [AddCommGroup M]
    [Module R M] {ι : Type wF} (𝒜 : ι → Set R) (𝓜 : ι → Set M) (T : Submonoid R) :
    Set (LocalizedModule T M) :=
  {x | ∃ (d : ι) (y : M) (h : T), y ∈ 𝓜 d ∧ (h : R) ∈ 𝒜 d ∧ mk y h = x}

end LocalizedModule
