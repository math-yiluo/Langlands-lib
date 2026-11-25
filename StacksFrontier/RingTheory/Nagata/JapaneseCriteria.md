# Localization and criteria for Japanese domains

Module `StacksFrontier.RingTheory.Nagata.JapaneseCriteria`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

The file develops ascent and descent of finite normalization (N-1) and the Japanese property (N-2), as well as a criterion that reduces N-2 to testing purely inseparable extensions.

- `isN1_and_isJapaneseRing_of_isLocalization` passes each property from a domain to a localization that is a domain.
- `isN1_and_isJapaneseRing_of_localizationSpan` descends each property from a family of domain localizations away from elements of a set generating the unit ideal.
- `isJapaneseRing_of_quasiFinite` gives N-2 for a domain `S` over a Noetherian N-2 domain `R` when the algebra map is injective and the algebra is both finite type and quasi-finite.
- `isJapaneseRing_iff_finite_integralClosure_isPurelyInseparable` says a Noetherian domain is Japanese exactly when the integral closure in each finite purely inseparable extension of its fraction field is module-finite.
- `module_finite_integralClosure_of_injective` descends finiteness of an integral closure along an injective map of algebras over a Noetherian base.

The localization arguments use a common fraction field, commutation of integral closure with localization, and locality of finite generation. Quasi-finite ascent uses Zariski's main theorem to cover the target by principal opens where the algebra agrees with a localization of a module-finite subalgebra.

For the purely inseparable criterion, pass to a finite normal closure of the test extension and take the fixed field of its automorphism group. The fixed field is purely inseparable over the base fraction field, and the normal closure is separable over the fixed field. Finiteness for separable extensions of Noetherian normal domains then gives finiteness in the normal closure, which descends to the test extension.

The Japanese statements use a common universe for the domain and its test fields. The quasi-finite theorem expresses injectivity by `FaithfulSMul R S`. The purely inseparable criterion allows any characteristic, reducing to N-1 in characteristic zero.

References are Tag 032F for the definitions, Tag 032G and Tag 032H for localization, Tag 032I for quasi-finite ascent, and Tag 032N for the purely inseparable criterion. The proof uses Tag 0307, Tag 00EO, Tag 030M, and Tag 032L. The references to Grothendieck and Dieudonné's *Éléments de géométrie algébrique* are EGA 0 23.1.1, EGA 0 23.1.2, and EGA II 6.3.10.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [032G](https://stacks.math.columbia.edu/tag/032G) | `isN1_and_isJapaneseRing_of_isLocalization` |  |
| [032H](https://stacks.math.columbia.edu/tag/032H) | `isN1_and_isJapaneseRing_of_localizationSpan` |  |
| [032N](https://stacks.math.columbia.edu/tag/032N) | `isJapaneseRing_iff_finite_integralClosure_isPurelyInseparable` |  |
| [032I](https://stacks.math.columbia.edu/tag/032I) | `isJapaneseRing_of_quasiFinite` |  |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | II 6.3.10 | `module_finite_integralClosure_of_isLocalization` | Locality on X |
| EGA | II 6.3.10 | `module_finite_integralClosure_of_localizationSpan` | Locality on X |
| EGA | 0 23.1.2 | `isJapaneseRing_iff_finite_integralClosure_isPurelyInseparable` |  |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/Nagata/JapaneseCriteria.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 3 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
