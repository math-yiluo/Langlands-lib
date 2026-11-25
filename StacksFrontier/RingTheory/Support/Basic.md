# Support under base change

Module `StacksFrontier.RingTheory.Support.Basic`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

For a finite module, support pulls back along the map of prime spectra induced by a ring map. The file also carries annihilators along a base change and gives a criterion for the support to be closed with quasi-compact complement.

- `IsBaseChange.support_eq_preimage_comap` assumes M is finite over R and f is an R-linear map that exhibits the S-module N as a base change of M along R → S. Then the support of N over S is the inverse image of the support of M over R. The abstract `IsBaseChange` hypothesis covers tensor products, quotients and localizations.
- `IsBaseChange.annihilator_le_comap_annihilator` sends the annihilator of M into that of N for any such base change, even for arbitrary modules and ring maps.
- `PrimeSpectrum.nontrivial_residueField_tensorProduct_baseChange`: if 𝔮 ⊆ S lies over 𝔭 ⊆ R and the fibre M ⊗_R κ(𝔭) is nonzero, then the fibre (S ⊗_R M) ⊗_S κ(𝔮) is nonzero; no finiteness is assumed.
- `support_isClosed_and_compl_isCompact_of_eq_zeroLocus_FG`: if the support of an R-module M is the zero locus V(I) of a finitely generated ideal I, then it is closed and its complement is quasi-compact.

One inclusion in the base-change equality uses the description of support as the annihilator's zero locus. For the reverse inclusion, Nakayama's lemma detects support of a finite module by its residue-field fibre, and a nonzero fibre stays nonzero under a residue field extension. The complement of V(I) is quasi-compact because I is finitely generated.

The annihilator result is the inclusion in the flat-base-change equality discussed under Tag 07T8. Support throughout is Mathlib's `Module.support`. The module docstring's list of main results also announces a closedness and compactness theorem for finitely presented modules with finitely generated annihilator, which the file does not contain.

The base-change result is Tag 0BUR. The file's comments point to the Mathlib declarations for Tags 00L1, 00L2, 00L3 and 0585. The file cites EGA 0 1.7.1, 0 1.7.2, 0 1.7.4, 0 5.2.2, 0 16.1.7, I 4.1.2, I 10.8.12, IV 5.1.12 and IV 8.9.1, as well as SGA 2 III 1.1 and SGA 3 VIA 2.1.3.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [0BUR](https://stacks.math.columbia.edu/tag/0BUR) | `support_eq_preimage_comap` |  |
| [00L2](https://stacks.math.columbia.edu/tag/00L2) | `Module.isClosed_support` | the support of a finite module is closed |
| [0585](https://stacks.math.columbia.edu/tag/0585) | `Module.support_eq_empty_iff` |  |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | 0 1.7.1 | `Module.support` | definition of Supp(M) |
| SGA | 2 III 1.1 | `Module.support` | the Supp M clause |
| EGA | 0 1.7.4 | `Module.support_eq_zeroLocus` |  |
| SGA | 3 VIA 2.1.3 | `Module.isClosed_support` | special case |
| EGA | 0 16.1.7 | `Module.isClosed_support` | partial |
| EGA | 0 5.2.2 | `Module.isClosed_support` | special case |
| EGA | I 4.1.2 | `Module.isClosed_support` | affine case |
| EGA | IV 5.1.12 | `Module.isClosed_support` | special case |
| EGA | IV 8.9.1 | `Module.isClosed_support` | closedness of Supp(F) |
| EGA | 0 1.7.2 | `Module.support_of_exact` |  |
| EGA | 0 1.7.1 | `Module.support_eq_empty_iff` | M = 0 ⇔ Supp M = ∅ |
| EGA | I 10.8.12 | `Module.support_quotient` | affine case, M finite |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/Support/Basic.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 7 declarations of the source file 4 are kept. The 3 left out are not needed by the results for which the extract is made: `mem_zeroLocus_annihilator_iff_localization_ne_zero`, `support_isClosed_and_compl_isCompact_of_finitePresentation`, `support_submodule_subset`.
- 1 command that is not a declaration is left out or changed with the declarations left out (`notes/reuse/stacks-extract/extract-commands.tsv.md`).
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 12 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
