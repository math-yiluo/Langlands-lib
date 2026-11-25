# The elementary tower of a finite extension

Module `FontaineWintenberger.APF.Tower.FiniteElementary`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let `K` be a complete discretely valued field and `L` a finite intermediate field of its separable closure. The positive upper breaks of `L/K` form a finite set; sorting them and taking the corresponding fixed fields, with `L` appended as last field, gives the finite elementary tower of `L/K`. The file constructs it and proves the finite versions of the statements of Wintenberger §1.4.1.

## Definitions

- `apfFiniteUpperBreaks K L : Finset ℝ`: the set of `u` with `IsAPFUpperBreak K L u`.
- `apfFiniteUpperBreak K L`: its increasing enumeration, an order embedding of `Fin card` into `ℝ`.
- `apfFiniteElementaryStage K L n`, for `n : Fin (card + 1)`: the field `apfFiniteStage K L` at the `n`-th break for `n < card`, and `L` itself for the last index.
- `apfFiniteElementaryLevel K L n`: `apfPsi K L` at the `n`-th break.

## Results

- `isAPF_iSup_fin`: the union of a finite monotone tower of finite subfields is APF (the finite alternative in Wintenberger's Remark 1.4.2).
- `finite_setOf_isAPFUpperBreak`: finiteness of the set of breaks.
- `apfSubgroup_eq_of_not_upperBreak`, `apfSubgroup_eq_at_finiteUpperBreak`, `apfSubgroup_eq_fixingSubgroup_after_finiteUpperBreaks`, `apfSubgroup_eq_fixingSubgroup_finiteElementaryStage_succ`: the APF product is constant on an interval without breaks; after the last break it is the fixing subgroup of `L`; on the plateau after the `n`-th break it is the fixing subgroup of stage `n.succ`.
- `strictMono_apfFiniteElementaryStage`, `iSup_apfFiniteElementaryStage`: the tower is strictly increasing with union `L`. The levels are positive and strictly increasing.
- `isElementaryStep_apfFiniteElementaryStage`: each step is an `IsElementaryStep` at its level.
- `apfRamificationBound_over_apfFiniteElementaryStage`: the ramification bound of `L` over the `n`-th stage (with its spectral norm) is the `n`-th level.
- `apfRamificationBound_eq_top_of_no_finiteUpperBreaks`: with `0 < apfRamificationBound K L` and no break, the bound is `⊤`.
- `apfRamificationBound_eq_apfFiniteElementaryLevel`: with a positive bound and at least one break, the bound is the level of index `0`.
- `apfStrictnessConstant_eq_iInf_apfFiniteElementaryLevel`: with a positive bound, the strictness constant is the infimum over `n` of level `n` divided by the degree over `K` of stage `n.succ`; for the empty tower both sides are `⊤`.
- `apfFiniteElementaryStage_zero` (for `IsPerfectResidueLocalField K`): stage `0` is `apfTameStage K L`.

## Proofs

Finiteness uses that some upper ramification group fixes `L` and that only finitely many breaks lie below a bound.
## Points to watch

- The residue field of `K` is assumed perfect, except in lemmas where the file omits that hypothesis.
- Indexing begins with Wintenberger's `K₁`; the unramified field `K₀` is the stage at parameter zero and is not in the tower.
- The formulas for the bound and the constant assume `0 < apfRamificationBound K L`.

## References

Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux; applications*, §1.4.1.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/APF/Tower/FiniteElementary.lean` (SHA-256 of the source file `ed032517c2333f004c27bda3c3254b7198926b835637157609a1337bcdca730d`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
