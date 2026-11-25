/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Lie.LieTheorem

/-!
# Common eigenvectors of solvable Lie algebras

Lie's theorem `LieModule.exists_nontrivial_weightSpace_of_isSolvable` provides a common
eigenvector for a solvable Lie algebra acting on a nonzero finite-dimensional module. This file
adds that the corresponding weight vanishes on the derived algebra.

## Main declarations

* `LieModule.exists_ne_zero_forall_lie_eq_smul_of_isSolvable`: a common eigenvector whose weight
  vanishes on `⁅L, L⁆`.

## Blueprint

`LieModule.exists_ne_zero_forall_lie_eq_smul_of_isSolvable` implements
`lemma-lie-s-theorem--1`.
-/

@[expose] public section

open LieAlgebra

namespace LieModule

variable (k L M : Type*) [Field k] [CharZero k] [LieRing L] [LieAlgebra k L]
  [AddCommGroup M] [Module k M] [LieRingModule L M] [LieModule k L M] [Module.Finite k M]

/-- **Common eigenvector for a solvable Lie algebra.** A solvable Lie algebra `L` acting
triangularizably on a nonzero finite-dimensional module `M` over a field of characteristic zero
has a common eigenvector `v`, with weight `χ` vanishing on the derived algebra `⁅L, L⁆`.
(blueprint: `lemma-lie-s-theorem--1`) -/
theorem exists_ne_zero_forall_lie_eq_smul_of_isSolvable [Nontrivial M] [IsSolvable L]
    [IsTriangularizable k L M] :
    ∃ (χ : Module.Dual k L) (v : M), v ≠ 0 ∧ (∀ x, ⁅x, v⁆ = χ x • v) ∧
      ∀ x ∈ derivedSeries k L 1, χ x = 0 := by
  obtain ⟨χ, hχ⟩ := exists_nontrivial_weightSpace_of_isSolvable k L M
  obtain ⟨⟨v, hv⟩, hv0⟩ := exists_ne (0 : weightSpace M χ)
  have hv0 : v ≠ 0 := fun h ↦ hv0 (Subtype.ext h)
  rw [mem_weightSpace] at hv
  refine ⟨χ, v, hv0, hv, fun x hx ↦ ?_⟩
  rw [derivedSeries_def, derivedSeriesOfIdeal_succ, derivedSeriesOfIdeal_zero,
    ← LieSubmodule.mem_toSubmodule, LieSubmodule.lieIdeal_oper_eq_linear_span'] at hx
  refine (Submodule.span_le (p := LinearMap.ker χ)).mpr ?_ hx
  rintro _ ⟨y, -, z, -, rfl⟩
  have h := hv ⁅y, z⁆
  rw [lie_lie, hv z, hv y, lie_smul, lie_smul, hv y, hv z, smul_smul, smul_smul, mul_comm,
    sub_self, eq_comm, smul_eq_zero] at h
  exact h.resolve_right hv0

end LieModule
