# The Japanese condition under ring isomorphisms

Module `StacksFrontier.RingTheory.Nagata.Japanese.NagataScheme`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

`IsJapaneseRing.of_ringEquiv` shows that the Japanese (N-2) condition is invariant under a ring isomorphism `e : R ≃+* S` of domains, even across universes. For a finite extension `L` of the fraction field of `S`, the proof makes `L` an algebra over `R` and over `FractionRing R` through `e` and the induced isomorphism of fraction fields. The private lemma `module_finite_of_ringEquiv_algebraMap`, by which module-finiteness of an algebra transfers along a ring isomorphism of the base, makes `L` finite over `FractionRing R`; the finiteness of the integral closure of `R` in `L` is then carried across `e` by `Module.Finite.integralClosure_of_ringEquiv` of the imported module `StacksFrontier.RingTheory.Nagata.Shrink`.

The module docstring still lists definitions of Japanese and Nagata rings and schemes and announces the criterion of Tag 033R, that a locally Noetherian scheme is Nagata exactly when its integral closed subschemes are Japanese; neither those definitions nor the criterion are in the file.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/Nagata/Japanese/NagataScheme.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 12 declarations of the source file 2 are kept. The 10 left out are not needed by the results for which the extract is made: `exists_isLocalizedModule_integralClosure`, `exists_japanese_localizationSpan_cover`, `isJapaneseRing_localizationAway`, `isJapaneseRing_of_isLocalizationAway`, `isJapaneseRing_of_localizationSpan`, `isJapaneseScheme_forall_affineOpens`, `nagata_backward_quotient_japanese`, `nagata_iff_integral_closed_subschemes_japanese`, `nagata_scheme_backward`, `nagata_scheme_forward`.
- 1 command that is not a declaration is left out or changed with the declarations left out (`notes/reuse/stacks-extract/extract-commands.tsv.md`).
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
