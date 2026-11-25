# Open subgroups of the idèle class group have finite index

Module `Langlands.ClassFieldTheory.Global.Artin.OpenSubgroupFiniteIndex`, name space
`Langlands.ClassFieldTheory.Global.Artin`. This file belongs to the Library and imports nothing
of the NYLL library: only the Library and Mathlib.

## Main declarations

```lean
theorem connectedSpace_units_nnreal : ConnectedSpace ℝ≥0ˣ

theorem positiveReal_mem_of_isOpen {K : Type u} [Field K] [NumberField K]
    (H : OpenSubgroup (IdeleClasses K)) (x : ℝ≥0ˣ) :
    ideleClassMap K (PositiveRealIdeles.full K x) ∈ H

def positiveRoot (K : Type u) [Field K] [NumberField K] (h : ℝ≥0ˣ) : ℝ≥0ˣ :=
  Units.map (NNReal.rpowMonoidHom ((Module.finrank ℚ K : ℝ)⁻¹)) h

theorem positiveRoot_pow {K : Type u} [Field K] [NumberField K] (h : ℝ≥0ˣ) :
    positiveRoot K h ^ Module.finrank ℚ K = h

theorem openSubgroup_sup_ker_eq_top {K : Type u} [Field K] [NumberField K]
    (H : OpenSubgroup (IdeleClasses K)) :
    (IdeleAbsoluteValue.ideleClass K).toMonoidHom.ker ⊔ H.toSubgroup = ⊤

theorem openSubgroup_finiteIndex (K : Type u) [Field K] [NumberField K]
    (H : OpenSubgroup (IdeleClasses K)) : H.toSubgroup.FiniteIndex
```

`openSubgroup_finiteIndex` is the clause `OpenIdeleClassSubgroupFiniteIndexStatement` of
`Langlands.Global.FiniteAbelianClassFieldStatement`; `OpenSubgroup` itself does not include
finiteness of the index.

## Proofs

- *`ℝ≥0ˣ` is connected*: Mathlib's `unitsHomeomorphNeZero` identifies it with the nonzero
  elements of `ℝ≥0`, which form the interval `Ioi 0`, a connected set.
- *Positive reals lie in every open subgroup*: the preimage of `H` under the continuous
  homomorphism `x ↦ ideleClassMap K (PositiveRealIdeles.full K x)` is an open subgroup of
  `ℝ≥0ˣ`, hence closed, hence everything since `ℝ≥0ˣ` is connected.
- *`H` and the norm-one classes generate*: for an idèle class `c` with absolute value `h`, the
  class `y` of `PositiveRealIdeles.full K (positiveRoot K h)` lies in `H` and has absolute value
  `positiveRoot K h ^ [K : ℚ] = h` (`PositiveRealIdeles.absoluteValue_full`), so `c y⁻¹` has
  absolute value `1` and `c = (c y⁻¹) y`.
- *Finite index*: the group is commutative, so `H` is normal and `relIndex_sup_right` gives
  `[C : H] = [C¹ : H ∩ C¹]`, where `C¹` is the kernel of the idèle absolute value
  `IdeleAbsoluteValue.ideleClass K`. The group `C¹` is compact
  (`NormOneIdeleClass.isCompact_ker_ideleClass`) and `H ∩ C¹` is open in it, so the quotient is
  finite (`Subgroup.quotient_finite_of_isOpen`).

## Declarations used

- From the Library: `IdeleClasses`, `ideleClassMap` (`Langlands/Global/Adelic.lean`);
  `PositiveRealIdeles.full`, `PositiveRealIdeles.absoluteValue_full`
  (`Langlands/Global/PositiveRealIdeles.lean`); `IdeleAbsoluteValue.ideleClass`,
  `IdeleAbsoluteValue.full` (`Langlands/Global/IdeleAbsoluteValue.lean`);
  `NormOneIdeleClass.isCompact_ker_ideleClass` (`Langlands/Global/NormOneIdeleClassCompact.lean`).
- From Mathlib: `unitsHomeomorphNeZero`, `isConnected_Ioi`, `Function.Surjective.connectedSpace`,
  `IsClopen.eq_univ`, `Subgroup.isClosed_of_isOpen`, `NNReal.rpowMonoidHom`,
  `NNReal.rpow_inv_natCast_pow`, `Subgroup.mul_mem_sup`, `Subgroup.relIndex_sup_right`,
  `Subgroup.relIndex_top_right`, `Subgroup.subgroupOf_isOpen`, `Subgroup.quotient_finite_of_isOpen`,
  `Subgroup.finiteIndex_of_finite_quotient`, `Subgroup.normal_of_isMulCommutative`.

## Sources

Neukirch, *Algebraic Number Theory*, Chapter VI, (1.6) (the norm-one idèle class group is
compact) and (1.8); Milne, *Class Field Theory*, Chapter V, Proposition 4.4.
