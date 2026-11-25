# The positive ramification breaks of an APF extension

Module `FontaineWintenberger.APF.Tower.Breaks`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let `K` be a complete discretely valued field and `L` an intermediate field of its separable closure that is APF (`IsAPFSubextension K L`). The file studies how the APF products `apfSubgroup K L u` (the subgroups `G_L G_K^u`) vary with `u`, and shows that for an infinite extension their positive breaks form an increasing unbounded sequence, as in Wintenberger §1.4.1.

## Definition

`IsAPFUpperBreak K L u`: `u > 0` and `apfSubgroup K L v ≠ apfSubgroup K L u` for every `v > u`. This is the set `B` of Wintenberger §1.4.1.

## Results

- `monotoneOn_apfSubgroup_index`: the index of `apfSubgroup K L u` is monotone in `u` on `u ≥ -1`.
- `apfSubgroup_eq_of_index_eq`: for `u, v ≥ -1`, equal indices give equal subgroups.
- `exists_apfSubgroup_eq_left`: for `u > 0` there is `0 < v < u` with `apfSubgroup K L w = apfSubgroup K L u` for all `w` in `(v, u]`. Requires the residue field of `K` to be perfect.
- `exists_lt_apfSubgroup_index`: if `L/K` is infinite, the indices are unbounded over `u > 0`.
- `isAPFUpperBreak_iff`: `u` is an upper break exactly when `u > 0` and the index function has a right jump at `u` (`IsRightJump`).
- `finite_setOf_isAPFUpperBreak_le`: only finitely many upper breaks lie below any given real number.
- `exists_apfUpperBreaks`: if `L/K` is infinite and the residue field of `K` is perfect, there is a strictly increasing sequence `b : ℕ → ℝ` of positive reals tending to infinity whose range is exactly the set of upper breaks, with `apfSubgroup K L u = apfSubgroup K L (b (n+1))` for `b n < u ≤ b (n+1)` and `apfSubgroup K L u = apfSubgroup K L (b 0)` for `0 < u ≤ b 0`.

## Proofs

Left-local constancy is obtained by passing to the finite stage `apfFiniteStage K L u`, then to its finite Galois normal closure, where the upper ramification groups of a finite Galois group are locally constant from the left (`exists_upperRamificationGroup_eq_left`). Unboundedness: if the indices were bounded, the products would be constant from some point on, and `L` would equal one finite stage, hence be finite. The sequence of breaks then comes from a general statement on right jumps of monotone integer-valued functions (`MonotoneOn.exists_strictMono_rightJumps`).

## Points to watch

- `IsAPFUpperBreak` concerns positive `u` only.
- The sequence of breaks is stated only for infinite `L/K`, and with a perfect residue field.

## References

Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux; applications*, §1.4.1.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/APF/Tower/Breaks.lean` (SHA-256 of the source file `ee10ba3c9f3538ac5c432b945b31465959975c6fed5b7aca8778dab481c23d23`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
