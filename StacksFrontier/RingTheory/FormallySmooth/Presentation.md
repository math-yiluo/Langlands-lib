# Formal smoothness from a formally smooth presentation

Module `StacksFrontier.RingTheory.FormallySmooth.Presentation`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

A surjection from a formally smooth algebra gives equivalent section, differential, and cotangent criteria for formal smoothness of the quotient.

For a tower R → P → S with P formally smooth over R and P → S surjective with kernel J, `Algebra.FormallySmooth.tfae_of_surjective` (also `Stacks.FormallySmooth.PresentationTFAE.solution`) shows that four conditions are equivalent.

- `Algebra.FormallySmooth R S`.
- The induced surjection P/J² → S has an R-algebra section.
- The conormal sequence is split short exact: J/J² → S ⊗_P Ω(P/R) is injective and S ⊗_P Ω(P/R) → Ω(S/R) has an S-linear section.
- Ω(S/R) is projective over S and `Algebra.H1Cotangent R S` vanishes.

The proof uses Mathlib’s splitting criterion for a formally smooth presentation, the injectivity criterion for vanishing of first cotangent homology, and splitting onto projective modules.

Mathlib defines `Algebra.FormallySmooth` by the cotangent condition, so the first condition is not the lifting property of Tag 00TI; the docstrings refer for it to a fuller statement that is not in this file.

## References

Stacks Project, Tag 031J, Tag 00TI, and Tag 00RU.

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | 0 20.4.9 | `Algebra.FormallySmooth.tfae_of_surjective` | discrete case |
| EGA | IV 17.2.3 | `Algebra.FormallySmooth.tfae_of_surjective` | (i), affine case |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/FormallySmooth/Presentation.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 3 declarations of the source file 2 are kept. The 1 left out are not needed by the results for which the extract is made: `Algebra.FormallySmooth.tfae_lifting_of_surjective`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 2 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
