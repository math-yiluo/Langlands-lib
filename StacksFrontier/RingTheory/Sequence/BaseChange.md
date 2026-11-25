# Regular sequences under faithfully flat base change

Module `StacksFrontier.RingTheory.Sequence.BaseChange`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Regularity of a finite sequence on a module can be checked after faithfully flat extension of scalars. Regularity here means injectivity of each element's action modulo its predecessors, together with nonvanishing of the quotient by the full sequence.

`RingTheory.Sequence.isRegular_map_algebraMap_iff_of_faithfullyFlat_of_isBaseChange` takes a faithfully flat R-algebra S and an R-linear map f from M to an S-module N with compatible scalar actions. If `IsBaseChange S f` holds, the image of a list in S is N-regular exactly when the original list is M-regular. The proof is in `Stacks.RegularSequence.FlatBaseChange.solution`. Its helpers give the analogous equivalences for a single injective scalar action and for weak regularity, which is the injectivity condition alone.

Faithfully flat tensoring preserves and reflects injectivity of multiplication by a scalar. Quotient by the first element commutes with base change, so induction gives the equivalence for weak regularity. Faithful flatness also detects whether the final quotient is zero.

The theorem uses an abstract base-change map through `IsBaseChange S f`. It assumes faithful flatness in both directions and thus includes flat local homomorphisms of local rings through the faithful flatness instance available for those maps.

## References

Tag 00LM. EGA 0 15.1.13, EGA 0 15.1.14, EGA 0 15.2.5, and SGA 3 VIIB 5.5.2 give related base-change statements, with the regularity result here in the faithfully flat case.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [00LM](https://stacks.math.columbia.edu/tag/00LM) | `isRegular_map_algebraMap_iff_of_faithfullyFlat_of_isBaseChange` |  |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | 0 15.1.13 | `isSMulRegular_tensorProduct_iff` | special case |
| EGA | 0 15.1.14 | `isSMulRegular_tensorProduct_iff` | special case |
| EGA | 0 15.1.13 | `isSMulRegular_algebraMap_iff_of_faithfullyFlat_of_isBaseChange` | special case |
| EGA | 0 15.1.14 | `isSMulRegular_algebraMap_iff_of_faithfullyFlat_of_isBaseChange` | special case |
| EGA | 0 15.1.14 | `isWeaklyRegular_map_algebraMap_iff_of_faithfullyFlat_of_isBaseChange` |  |
| SGA | 3 VIIB 5.5.2 | `isWeaklyRegular_map_algebraMap_iff_of_faithfullyFlat_of_isBaseChange` | partial |
| EGA | 0 15.1.14 | `isRegular_map_algebraMap_iff_of_faithfullyFlat_of_isBaseChange` | converse (ff case) |
| EGA | 0 15.2.5 | `isRegular_map_algebraMap_iff_of_faithfullyFlat_of_isBaseChange` | affine, faithfully flat |
| EGA | 0 15.1.13 | `isRegular_map_algebraMap_iff_of_faithfullyFlat_of_isBaseChange` | special case |
| SGA | 3 VIIB 5.5.2 | `isRegular_map_algebraMap_iff_of_faithfullyFlat_of_isBaseChange` | special case |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/Sequence/BaseChange.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 10 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
