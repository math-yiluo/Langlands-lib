# Hilbert's formula for the different in terms of lower ramification groups

Module `FontaineWintenberger.Ramification.Different.Hilbert`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

The file rewrites the sum over nonidentity automorphisms that computes the exponent of the different as a sum of the numbers `|G_n| − 1` over the lower ramification groups, and states Hilbert's formula for a finite Galois extension of a complete discretely valued field in both forms.

## Counting lemmas

Here `B` is a discrete valuation ring (a domain) and `G` a finite group acting on `B` by ring automorphisms (`MulSemiringAction G B`). The function `ramificationOrder (R := B) G g`, with values in `ℕ∞`, and the subgroups `lowerRamificationGroup G (maximalIdeal B) n` come from earlier files of the library; the file uses that `g` lies in the `n`-th lower group exactly when `n + 1 ≤ ramificationOrder g`.

- `sum_ramificationOrder_eq_sum_lower_card`: if `N` bounds `ramificationOrder g` for every `g ≠ 1`, then the sum of `ramificationOrder g` over `g ≠ 1` equals the sum over `n < N` of `Nat.card (lowerRamificationGroup G (maximalIdeal B) n) − 1`. The proof writes each order as a sum of indicators and exchanges the two sums.
- `exists_sum_ramificationOrder_eq_sum_lower_card`: if the action is faithful, there is an `N` such that the lower groups are trivial from index `N` on and the equality above holds for this `N`. It rests on the eventual triviality of the lower groups (`lowerRamificationGroup_eventually_eq_bot`).

## Hilbert's formula

Let `K` be a complete discretely valued field in the library's sense (`NontriviallyNormedField K` with `IsCompleteDiscreteValuedField K`) with perfect residue field, `L` a finite Galois extension, and `OL = spectralIntegerRing K L` its ring of integers.

- `spectralIntegerRing_different_order_eq_sum_ramificationOrder`: the multiplicity of the maximal ideal of `OL` in `differentIdeal 𝒪[K] OL` equals the sum of `ramificationOrder g` over the nonidentity elements `g` of `L ≃ₐ[K] L`.
- `spectralIntegerRing_different_order_eq_sum_lower_card`: there is an `N` such that the lower ramification groups of `L ≃ₐ[K] L` are trivial from index `N` on, and the same multiplicity equals the sum over `n < N` of `|G_n| − 1`.

The first is obtained from the formula for monogenic extensions (`differentIdeal_order_eq_sum_ramificationOrder`) and the existence of a generator of `OL` over `𝒪[K]` (`spectralIntegerRing_exists_generator`), both proved elsewhere in the library; the second combines it with the counting lemma.

## What to watch for

- The residue field of `K` is assumed perfect, and `L/K` is finite Galois; the sum runs over the full Galois group, not over the inertia group.
- The second formula is an existence statement with a finite cutoff `N`, not an infinite sum.
- Both sides lie in `ℕ∞`; the subtraction `|G_n| − 1` is taken in `ℕ`.
- `spectralIntegerRing` and `ramificationOrder` are the library's own notions.

## References

Serre, *Local Fields*, Chapter IV.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/Ramification/Different/Hilbert.lean` (SHA-256 of the source file `5af3b75e860d6bab35277bc57eb1906406e49869641b29097797ca7bc4ab8568`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
