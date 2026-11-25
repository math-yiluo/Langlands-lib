# Noetherianity of adic completions

Module `StacksFrontier.RingTheory.AdicCompletion.NoetherianRing.PowerSeriesSurjection`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

The completion of a commutative Noetherian ring along any ideal is Noetherian. The argument realizes the completion as a quotient of a formal power series ring in finitely many variables.

`Stacks.AdicCompletion.NoetherianRing.solution` proves the assertion for any ideal I of R, and the instance `AdicCompletion.stacks_isNoetherianRing` installs it for `AdicCompletion I R`. The second module docstring names this instance without the prefix `stacks_`.

The private theorem `exists_ringHom_adicCompletion` constructs a map from the J-adic completion of A to the I-adic completion of B whenever a ring map f sends J into I. It is compatible with f on the original rings. The private `surjective_of_comp_algebraMap_eq` shows that such a compatible map is surjective when f is surjective, J is finitely generated, and I is its image ideal.

The construction uses the induced maps A/Jⁿ → B/Iⁿ at each level. For surjectivity, the proof uses precompleteness of the source and separatedness of the target, reducing to surjectivity modulo the extended ideal. There, every class in the target completion has a representative from B. Applying this to polynomial evaluation on a finite set of generators of I and identifying the completion at the variables with the power series ring gives the desired surjection. Noetherianity then passes to the quotient.

Tag 0316. The construction of the map on completions is cited as part of SGA 1 IV 5.8.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [0316](https://stacks.math.columbia.edu/tag/0316) | `AdicCompletion.stacks_isNoetherianRing` | Stated as an instance for `IsNoetherianRing (AdicCompletion I R)`, Mathlib's spelling of the completion `R^∧ = lim_n R/Iⁿ`. See the module docstring. |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| SGA | 1 IV 5.8 | `exists_ringHom_adicCompletion` | partial |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/AdicCompletion/NoetherianRing/PowerSeriesSurjection.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- Renamed, the source's name being declared elsewhere as well (`licenses/Stacks/STX-RENAMES.tsv.md`): `AdicCompletion.isNoetherianRing` is `AdicCompletion.stacks_isNoetherianRing` here.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- One reference to EGA or SGA, written in the source as an attribute of that library, is taken out of the Lean text and listed above.
