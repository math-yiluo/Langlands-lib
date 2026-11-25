# Regularity from adic formal smoothness

Module `StacksFrontier.RingTheory.FormallySmooth.RegularLocal`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

A Noetherian local algebra over a field is regular if its structure map is formally smooth for the topology defined by its maximal ideal.

`RingHom.FormallySmoothTop.isRegularLocalRing_of_maximalIdeal` takes a field k, a Noetherian local k-algebra A, and the continuous square-zero lifting property for k → A. It uses the discrete topology on k and the maximal-ideal-adic topology on A. The conclusion is `IsRegularLocalRing A`.

The proof restricts scalars to the perfect prime field and uses the Cohen structure theorem and minimal generators of the maximal ideal to present the completion by a power series ring, with kernel in the square of the maximal ideal of that ring. Continuous lifting yields a section, the endomorphism criterion for maps congruent to the identity modulo the square makes the surjection an isomorphism, and regularity descends along the flat local completion map.

The lifting hypothesis `h` tests rings in the join of the universes of k and A.

## References

Stacks Project, Tag 07EI. EGA 0 19.6.5 and 0 22.5.8 for the regularity implication.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [07EI](https://stacks.math.columbia.edu/tag/07EI) | `isRegularLocalRing_of_maximalIdeal` |  |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | 0 19.6.5 | `isRegularLocalRing_of_maximalIdeal` | A regular (k'=k) |
| EGA | 0 22.5.8 | `isRegularLocalRing_of_maximalIdeal` | a) ⇒ A regular |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/FormallySmooth/RegularLocal.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 9 declarations of the source file 8 are kept. The 1 left out are not needed by the results for which the extract is made: `RingHom.FormallySmoothTop.exists_section_of_formallySmooth_of_quotient`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 2 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
