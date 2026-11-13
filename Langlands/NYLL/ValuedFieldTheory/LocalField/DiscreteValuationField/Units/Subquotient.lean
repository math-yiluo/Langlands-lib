/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.Units.Filtration

/-!
# Principal-unit quotient and subquotient data

Adapted by Worker 321 from NYLL M120.024–025 and M120.028–032 at commit
`fbd320cd8b1b06487c58227e92eb135794267709`. Modifications: prefix the
namespace by `Langlands.NYLL`, isolate the listed data, and import their
paired filtration module in place of the original Mathlib import list.
-/

namespace Langlands.NYLL.LocalFieldTheory

universe u v

open scoped BigOperators

namespace DiscreteValuationField

namespace AntitoneSubgroupFiltration

variable {G : Type u} [Group G] (U : AntitoneSubgroupFiltration G)

/-- The class of `U^m` inside `G ⧸ U^n`.  For `m ≤ n`, this is the kernel of
the natural map `G ⧸ U^n →* G ⧸ U^m`. -/
def principalUnitSubgroupClassInQuotient (m n : ℕ)
    [(U.principalUnitSubgroup n).Normal] :
    Subgroup (G ⧸ U.principalUnitSubgroup n) :=
  Subgroup.map (QuotientGroup.mk' (U.principalUnitSubgroup n))
    (U.principalUnitSubgroup m)

/-- The subgroup appearing in `(U.principalUnitSubgroupClassInQuotient m n).Normal` is normal. -/
instance principalUnitSubgroupClassInQuotient_normal
    (m n : ℕ) [(U.principalUnitSubgroup n).Normal]
    [(U.principalUnitSubgroup m).Normal] :
    (U.principalUnitSubgroupClassInQuotient m n).Normal := by
  dsimp [principalUnitSubgroupClassInQuotient]
  infer_instance

/-- The subquotient `U^m/U^n` of a principal-unit filtration.  Under
`m ≤ n`, antitonicity makes this the usual quotient of `U^m` by `U^n`. -/
def principalUnitSubquotient (m n : ℕ) : Type u :=
  U.principalUnitSubgroup m ⧸
    (U.principalUnitSubgroup n).subgroupOf (U.principalUnitSubgroup m)

/--
Equips the target with its canonical `Group` structure, namely `Group (U.principalUnitSubquotient
m n)`.
-/
instance principalUnitSubquotientGroup
    (m n : ℕ) [(U.principalUnitSubgroup n).Normal] :
    Group (U.principalUnitSubquotient m n) := by
  change Group
    (U.principalUnitSubgroup m ⧸
      (U.principalUnitSubgroup n).subgroupOf
        (U.principalUnitSubgroup m))
  infer_instance

/-- Explicit access to the concrete quotient representation. -/
def principalUnitSubquotientConcreteEquiv
    (m n : ℕ) [(U.principalUnitSubgroup n).Normal] :
    U.principalUnitSubquotient m n ≃*
      (U.principalUnitSubgroup m ⧸
        (U.principalUnitSubgroup n).subgroupOf
          (U.principalUnitSubgroup m)) := by
  change
    (U.principalUnitSubgroup m ⧸
        (U.principalUnitSubgroup n).subgroupOf
          (U.principalUnitSubgroup m)) ≃*
      (U.principalUnitSubgroup m ⧸
        (U.principalUnitSubgroup n).subgroupOf
          (U.principalUnitSubgroup m))
  exact MulEquiv.refl _

/-- A subquotient of a commutative principal-unit filtration retains the
commutative group structure of its concrete quotient representation. -/
instance principalUnitSubquotientCommGroup
    {H : Type u} [CommGroup H] (V : AntitoneSubgroupFiltration H)
    (m n : ℕ) [(V.principalUnitSubgroup n).Normal] :
    CommGroup (V.principalUnitSubquotient m n) :=
  { (inferInstance : Group (V.principalUnitSubquotient m n)) with
    mul_comm := fun x y => by
      apply (V.principalUnitSubquotientConcreteEquiv m n).injective
      simp only [map_mul]
      exact mul_comm _ _ }

/-- The canonical class map `U^m → U^m/U^n`. -/
def principalUnitSubquotientMk
    (m n : ℕ) [(U.principalUnitSubgroup n).Normal] :
    U.principalUnitSubgroup m →* U.principalUnitSubquotient m n := by
  change U.principalUnitSubgroup m →*
    (U.principalUnitSubgroup m ⧸
      (U.principalUnitSubgroup n).subgroupOf
        (U.principalUnitSubgroup m))
  exact QuotientGroup.mk'
    ((U.principalUnitSubgroup n).subgroupOf
      (U.principalUnitSubgroup m))

end AntitoneSubgroupFiltration

end DiscreteValuationField

end Langlands.NYLL.LocalFieldTheory
