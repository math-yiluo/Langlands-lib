# Characterization of finite elementary towers

Module `FontaineWintenberger.APF.Tower.FiniteCharacterization`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let `K` be a complete discretely valued field. The file proves the finite case of Wintenberger 1.4.2: a strictly increasing finite tower of finite subfields of the separable closure with elementary successive steps and tame first field is the canonical finite elementary tower of its last field, with the same levels.

## Results

The first part works with an abstract profile. Given a strictly increasing tower `E : Fin (m+1) → FiniteIntermediateField K (SeparableClosure K)` and strictly increasing positive reals `b : Fin m → ℝ`, suppose that the APF products of the last field `E (Fin.last m)` satisfy:

- at `b n` the product is the fixing subgroup of `E n.castSucc` (`hlevel`);
- for `u > b n` and `u ≤ b k` for all `k > n`, it is the fixing subgroup of `E n.succ` (`hplateau`);
- for `u > 0` below all `b n`, it is the fixing subgroup of `E 0` (`hinitial`).

Then:

- `isAPFUpperBreak_iff_mem_range_of_finite_profiles`: the upper breaks of the last field are exactly the values `b n`.
- `card_apfFiniteUpperBreaks_eq_of_finite_profiles`: the last field has exactly `m` positive upper breaks.
- `apfFiniteUpperBreak_eq_of_finite_profiles`: the sorted enumeration `apfFiniteUpperBreak` of these breaks is `b`.
- `apfFiniteElementaryStage_eq_of_finite_profiles`: the canonical stages `apfFiniteElementaryStage` of the last field are the `E n`, including the last one.

The main theorem, with the residue field of `K` perfect:

- `exists_apfFiniteElementaryStage_eq_of_isElementaryStep` (Wintenberger 1.4.2, finite case): let `E` be strictly increasing, `i : Fin m → ℝ` strictly increasing, each `E n.succ` over `E n.castSucc` an `IsElementaryStep` of level `i n`, and `E 0` fixed by every upper ramification group `G_K^u` with `u > 0`. Then the last field has `m` positive upper breaks, its canonical stages are the `E n`, and its canonical levels `apfFiniteElementaryLevel` are the `i n`.

## Proofs

The profile hypotheses are supplied by `finite_elementary_tower_profiles` with `b n = apfPhi K (E n.castSucc) (i n)`. The breaks are identified by locating a parameter `u` relative to the `b n`; a strict inclusion of fields forbids equality of the products across a `b n`. Sorting uses uniqueness of the order embedding of a finite set (`Finset.orderEmbOfFin_unique`). The levels are recovered since `apfPsi` inverts `apfPhi`.

## Points to watch

- The canonical tower is indexed by `Fin (card + 1)` with `card` the number of breaks of the last field; the statements pass between this index type and `Fin (m+1)` by `Fin.cast` along the proved equality of cardinalities, which is why the main theorem is an existence statement over that equality.
- The case `m = 0` is included.

## References

Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux; applications*, §§1.4.1–1.4.2.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/APF/Tower/FiniteCharacterization.lean` (SHA-256 of the source file `81260fae330519e3812c4281061f7c0a815b21222f389887890ae74996d9ed91`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
