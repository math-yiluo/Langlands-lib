# Faithful flatness of adic completion

Module `StacksFrontier.RingTheory.AdicCompletion.Flat.LimitExactness`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

The file proves faithful flatness of adic completion over a commutative Noetherian ring.

`AdicCompletion.faithfullyFlat_of_le_ringJacobson` gives faithful flatness of the I-adic completion over R, as the class `Module.FaithfullyFlat`, if I lies in the Jacobson radical. The maximal-ideal completion of a Noetherian local ring is a case of this sufficient condition. The proof uses Mathlib's `AdicCompletion.flat_of_isNoetherian` and the surjection onto R/I to check that every maximal ideal extends to a proper ideal.

A comment points to Mathlib's completion results for finite modules: `AdicCompletion.map_injective`, `AdicCompletion.map_surjective`, `AdicCompletion.map_exact` and `AdicCompletion.ofTensorProduct_bijective_of_finite_of_isNoetherian`. The module docstring also announces that completion preserves short exact sequences, and results on limits of towers of modules; neither is in the file.

## References

The faithful flatness statement is Tag 00MC. Mathlib supplies the flatness part of Tag 00MB and the completion-map and tensor results of Tag 00MA. Related references are EGA 0 7.3.1, EGA 0 7.3.3, EGA 0 7.3.5, EGA 0 7.7.8, EGA IV 7.8.3, EGA IV 8.11.4, SGA 1 IV 3.1, SGA 1 IV 3.2, and SGA 3 VIIB 5.5.2.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [00MC](https://stacks.math.columbia.edu/tag/00MC) | `AdicCompletion.faithfullyFlat_of_le_ringJacobson` | Stated as the class `Module.FaithfullyFlat R (AdicCompletion I R)`, the shape of the flatness half `AdicCompletion.flat_of_isNoetherian`; the `in particular` is the case `I = 𝔪`. See the module docstring. |
| [00MA](https://stacks.math.columbia.edu/tag/00MA) | `AdicCompletion.map_injective` | (1), and the injectivity half of (2) |
| [00MA](https://stacks.math.columbia.edu/tag/00MA) | `AdicCompletion.map_surjective` | (2): surjectivity of the completed second map |
| [00MA](https://stacks.math.columbia.edu/tag/00MA) | `AdicCompletion.map_exact` | (2): exactness in the middle of the completed sequence |
| [00MA](https://stacks.math.columbia.edu/tag/00MA) | `AdicCompletion.ofTensorProduct_bijective_of_finite_of_isNoetherian` | (3) |
| [00MB](https://stacks.math.columbia.edu/tag/00MB) | `AdicCompletion.flat_of_isNoetherian` | (1) |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | 0 7.3.5 | `AdicCompletion.faithfullyFlat_of_le_ringJacobson` | (a) => (b) |
| SGA | 1 IV 3.2 | `AdicCompletion.faithfullyFlat_of_le_ringJacobson` | if direction |
| SGA | 1 IV 3.1 | `AdicCompletion.faithfullyFlat_of_le_ringJacobson` | flatness, I ⊆ rad |
| SGA | 3 VIIB 5.5.2 | `AdicCompletion.faithfullyFlat_of_le_ringJacobson` | partial |
| EGA | 0 7.3.1 | `AdicCompletion.map_surjective` | v̂ surjective |
| SGA | 3 VIIB 5.5.2 | `AdicCompletion.map_exact` | partial |
| EGA | 0 7.3.3 | `AdicCompletion.map_exact` | partial |
| EGA | 0 7.3.1 | `AdicCompletion.map_exact` | Noetherian, finite mods |
| EGA | 0 7.3.3 | `AdicCompletion.ofTensorProduct_bijective_of_finite_of_isNoetherian` |  |
| EGA | 0 7.7.8 | `AdicCompletion.ofTensorProduct_bijective_of_finite_of_isNoetherian` | B = Â |
| SGA | 1 IV 3.1 | `AdicCompletion.flat_of_isNoetherian` |  |
| SGA | 3 VIIB 5.5.2 | `AdicCompletion.flat_of_isNoetherian` | flatness of Â over A |
| EGA | 0 7.3.3 | `AdicCompletion.flat_of_isNoetherian` |  |
| EGA | IV 7.8.3 | `AdicCompletion.flat_of_isNoetherian` | (v) |
| EGA | IV 8.11.4 | `AdicCompletion.flat_of_isNoetherian` | partial |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/AdicCompletion/Flat/LimitExactness.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 31 declarations of the source file 1 are kept. The 30 left out are not needed by the results for which the extract is made; `licenses/Stacks/STX-MANIFEST.tsv.md` lists them.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 15 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
