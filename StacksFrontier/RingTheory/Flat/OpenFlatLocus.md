# Openness of the relative flat locus

Module `StacksFrontier.RingTheory.Flat.OpenFlatLocus`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

This file proves that flatness over a base ring is an open condition on the prime localizations of a finitely presented module over a finitely presented algebra.

- For a finitely presented commutative R-algebra S and a finitely presented S-module M with compatible R-action, `Module.isOpen_setOf_flat_localizedModule_atPrime` proves that the primes q of S for which M localized at q is R-flat form an open subset of Spec S.
- `Module.isOpen_setOf_flat_localizedModule_atPrime_of_isNoetherianRing` gives openness for a Noetherian base R, a finite type R-algebra S, and a finite S-module M.
- In `Algebra.FiniteTypeSystem`, `exists_flat_localized_stage` descends flatness at q to a stage Rᵢ → Sᵢ at the contracted prime. It works with a model S = R ⊗_{R₀} S₀, where R₀ is a finite type ℤ-subring of R and S₀ a finite type R₀-algebra, and a finite S₀-module P, and assumes that S_q ⊗_{S₀} P is R-flat.

The Noetherian case pulls back the known polynomial-ring flat locus along a quotient presentation of S. In general, finite presentation gives a model over a finite type ℤ-subring. Localizing the directed systems at the contracted primes and tensoring with the model module commute with the colimit, so the local flatness descent theorem gives a Noetherian stage with flatness at the corresponding prime. The pushout comparison `Module.flat_localization_atPrime_tensor_of_isPushout` then carries an open neighbourhood of that prime back to Spec S.

The public statement allows R, S and M in independent universes. Its proof uses `Shrink` to replace S by an isomorphic R-algebra in the universe of R for the colimit argument. In `Algebra.FiniteTypeSystem.exists_flat_localized_stage`, by contrast, the rings R, S and S₀ and the model module P must lie in a single universe. The module docstring also lists, among its main results, two theorems carrying flatness at a prime up the system and to its colimit; they are not in this file.

## References

Tag 00RC gives openness. Related references are EGA IV 11.3.1 and SGA 1 IV 6.10 in the affine case, and EGA IV 11.1.6 and 11.3.3 for C = B.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [00RC](https://stacks.math.columbia.edu/tag/00RC) | `Module.isOpen_setOf_flat_localizedModule_atPrime` |  |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | IV 11.3.1 | `Module.isOpen_setOf_flat_localizedModule_atPrime` | U open, affine case |
| SGA | 1 IV 6.10 | `Module.isOpen_setOf_flat_localizedModule_atPrime` | affine case |
| EGA | IV 11.1.6 | `Module.isOpen_setOf_flat_localizedModule_atPrime` | case C = B |
| EGA | IV 11.3.3 | `Module.isOpen_setOf_flat_localizedModule_atPrime` | case C = B |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/Flat/OpenFlatLocus.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 47 declarations of the source file 44 are kept. The 3 left out are not needed by the results for which the extract is made: `Algebra.FiniteTypeSystem.flat_localized_of_le`, `Algebra.FiniteTypeSystem.flat_localized_of_stage`, `Module.exists_away_flat_of_flat_atPrime`.
- 2 commands that are not declarations are left out or changed with the declarations left out (`notes/reuse/stacks-extract/extract-commands.tsv.md`).
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 4 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
