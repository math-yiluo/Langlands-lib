/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Lie.Killing
public import Mathlib.Algebra.Lie.Semisimple.Basic

/-!
# Solvability, the radical, the centre and the Killing form

The basic notions of Lie algebras used in the study of monodromy groups, in the form in which they
are stated in the blueprint, deduced from their Mathlib definitions.

## Main declarations

* `LieAlgebra.isSolvable_iff_exists_derivedSeries_eq_bot`: a Lie algebra is solvable if and only
  if a term of its derived sequence vanishes.
* `LieIdeal.isSolvable_sup`: the sum of two solvable ideals is solvable.
* `LieAlgebra.isGreatest_radical`: the radical is the largest solvable ideal.
* `LieAlgebra.mem_center_iff_forall_lie_eq_zero`: the centre consists of the elements whose
  brackets with all elements vanish.
* `LieAlgebra.hasTrivialRadical_iff_forall_isSolvable_eq_bot`: a Lie algebra is semisimple (has
  trivial radical) if and only if it has no nonzero solvable ideal.
* `LieAlgebra.killingForm_apply_eq_trace`: the Killing form is `B(x, y) = Tr(ad x ∘ ad y)`.
-/

@[expose] public section

namespace LieAlgebra

variable (R L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]

/-- A Lie algebra `L` is solvable if and only if its derived sequence `D⁰ L = L`,
`Dⁿ⁺¹ L = ⁅Dⁿ L, Dⁿ L⁆` reaches `0`.
(blueprint: `def-wf-lie-algebra`) -/
theorem isSolvable_iff_exists_derivedSeries_eq_bot :
    IsSolvable L ↔ ∃ n, derivedSeries R L n = ⊥ :=
  isSolvable_iff R L

/-- The radical of a Noetherian Lie algebra, defined as the supremum of all solvable ideals, is
the largest solvable ideal: it is solvable and contains every solvable ideal.
(blueprint: `def-wf-lie-radical-centre`, `det-d-lie`) -/
theorem isGreatest_radical [IsNoetherian R L] :
    IsGreatest {I : LieIdeal R L | IsSolvable I} (radical R L) :=
  ⟨radicalIsSolvable R L, fun I (hI : IsSolvable I) ↦
    (LieIdeal.solvable_iff_le_radical R L I).mp hI⟩

variable {R L} in
/-- The centre `𝔷(L)` of a Lie algebra consists of the elements `x` with `⁅x, y⁆ = 0` for all
`y`.
(blueprint: `def-wf-lie-radical-centre`) -/
theorem mem_center_iff_forall_lie_eq_zero (x : L) : x ∈ center R L ↔ ∀ y : L, ⁅x, y⁆ = 0 := by
  rw [LieModule.mem_maxTrivSubmodule]
  exact forall_congr' fun y ↦ by rw [← lie_skew, neg_eq_zero]

/-- A Lie algebra is semisimple, i.e. has trivial radical, if and only if it has no nonzero
solvable ideal.
(blueprint: `def-wf-semisimple-lie-algebra`) -/
theorem hasTrivialRadical_iff_forall_isSolvable_eq_bot :
    HasTrivialRadical R L ↔ ∀ I : LieIdeal R L, IsSolvable I → I = ⊥ :=
  hasTrivialRadical_iff_no_solvable_ideals R L

/-- The Killing form of a finite free Lie algebra is `B(x, y) = Tr(ad x ∘ ad y)`.
(blueprint: `det-d-lie`) -/
theorem killingForm_apply_eq_trace [Module.Free R L] [Module.Finite R L] (x y : L) :
    killingForm R L x y = LinearMap.trace R L (ad R L x ∘ₗ ad R L y) :=
  LieModule.traceForm_apply_apply R L L x y

end LieAlgebra

namespace LieIdeal

open LieAlgebra

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

/-- The sum of two solvable ideals of a Lie algebra is solvable.
(blueprint: `proposition-lie-algebras-faithful-semisimple-representation--1`) -/
theorem isSolvable_sup {I J : LieIdeal R L} (hI : IsSolvable I) (hJ : IsSolvable J) :
    IsSolvable ↥(I ⊔ J) :=
  isSolvableAdd (R := R) (I := I) (J := J)

end LieIdeal
