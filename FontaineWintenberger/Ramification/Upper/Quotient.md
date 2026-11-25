# Herbrand's quotient theorem and transitivity of the Herbrand function

Module `FontaineWintenberger.Ramification.Upper.Quotient`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let `K` be a complete discretely valued field with perfect residue field, `L/K` a finite Galois extension with group `G`, `H` a normal subgroup, and `F` its fixed field. Write `B` for `spectralIntegerRing K L`, `A` for the valuation ring of `F`, and `D` for the group of automorphisms of `F`, given as the decomposition subgroup of `A`. The file proves Herbrand's theorem on lower ramification groups of the quotient and the transitivity `φ(L/K) = φ(F/K) ∘ φ(L/F)`.

## Main results

- `mem_lowerRamificationGroupReal_iff_le_toNat`: for a group acting on a discrete valuation ring, an element of finite order `i` lies in the real-indexed lower group at `t` if and only if `t ≤ i - 1`.
- `fixedField_map_lowerRamificationGroupReal`: for `t ≥ -1`, restriction to `F` maps the lower group of `G` at `t` onto the lower group of `D` at `herbrandFunction H t`, the Herbrand function of `H` acting on `B`.
- `fixedField_quotient_lowerRamificationGroupReal`: the same through the quotient by `H` and `fixedFieldDecompositionQuotientEquiv`.
- `fixedField_card_lowerRamificationGroupReal`: for `t ≥ -1`, the order of the lower group of `G` at `t` is the product of the order of the lower group of `H` at `t` and that of `D` at `herbrandFunction H t`.
- `fixedField_card_lowerRamificationGroup_zero`: the orders of the inertia groups of `G`, `H`, `D` multiply accordingly.
- `fixedField_herbrand_slope_mul`, `fixedField_exists_herbrand_comp_derivative_breaks`: the slopes of the three Herbrand functions multiply; outside a finite set of `t > 0`, the composite of the Herbrand functions of `D` and of `H` has at `t` the slope of that of `G`.
- `fixedField_herbrandFunction_transitivity`: for every real `t`, `herbrandFunction G t = herbrandFunction D (herbrandFunction H t)`.
- `fixedField_inverseHerbrandFunction_transitivity`: for `u ≥ -1`, the inverse Herbrand function of `G` at `u` is that of `H` applied to that of `D` at `u`.

## Proofs

The quotient theorem follows from `exists_fixedField_order_eq_herbrand` in the file on coset maxima: a non-trivial `τ` in `D` has a lift `s` of largest order, with `i(τ) - 1 = φ_H(i(s) - 1)`; the Herbrand function is strictly increasing. The cardinality formula counts a subgroup through the kernel `H` of the restriction and its image. Transitivity is obtained by integration: the composite is continuous and has the right derivative outside a finite set, so Mathlib's fundamental theorem of calculus with countably many exceptional points applies.

## Points to watch

- The residue field of `K` is assumed perfect, not finite.
- Transitivity is stated for all real `t`; the other results for arguments at least `-1`.
- Lower groups carry a real index, with the library's convention.

## References

Serre, *Local Fields*, Chapter IV.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/Ramification/Upper/Quotient.lean` (SHA-256 of the source file `6e050f493d3b594ce604dc65aed737c254414e01663275c4641365bce5d7a908`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
