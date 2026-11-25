# Splitting of Kähler differentials in a formally smooth tower

Module `StacksFrontier.RingTheory.Kaehler.BaseChange`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

For a tower R → A → B of commutative rings with B formally smooth over A, this file shows that the sequence 0 → B ⊗[A] Ω[A/R] → Ω[B/R] → Ω[B/A] → 0 is split exact.

- `KaehlerDifferential.exists_retraction_mapBaseChange` gives a B-linear retraction of the map B ⊗[A] Ω[A/R] → Ω[B/R]. It is proved as `Stacks.KaehlerDifferential.TowerSplitting.solution`.

By `Algebra.formallySmooth_iff`, Ω[B/A] is projective and `H₁(L_{B⁄A}) = 0`; the latter yields injectivity by `KaehlerDifferential.mapBaseChange_injective` from `StacksFrontier.RingTheory.Kaehler.JacobiZariski`, and projectivity splits the sequence.

The retraction supplies the injectivity and splitting assertions of Tag 031K. Exactness at the middle and surjectivity are Mathlib's `KaehlerDifferential.exact_mapBaseChange_map` and `KaehlerDifferential.map_surjective`. A docstring of the file gives base change along a pushout, Tag 00RV, as the Mathlib results `KaehlerDifferential.tensorKaehlerEquivBase` and `KaehlerDifferential.tensorKaehlerEquiv`. The module docstring also announces two localization results that are not in the file.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [031K](https://stacks.math.columbia.edu/tag/031K) | `KaehlerDifferential.exists_retraction_mapBaseChange` | Split short exactness, i.e. the two assertions of the tag that are not already in Mathlib (exactness at `Ω_{C/A}` is `KaehlerDifferential.exact_mapBaseChange_map` and surjectivity is `KaehlerDifferential.map_surjective`), stated as the existence of a retraction of the injection: that is at once its injectivity and the splitting. See the module docstring. |
| [00RV](https://stacks.math.columbia.edu/tag/00RV) | `KaehlerDifferential.tensorKaehlerEquivBase` | for an arbitrary pushout square, with the tensor factors in the other   order |
| [00RV](https://stacks.math.columbia.edu/tag/00RV) | `KaehlerDifferential.tensorKaehlerEquiv` | the variant over the base-changed algebra |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | 0 20.5.7 | `KaehlerDifferential.exists_retraction_mapBaseChange` | (ii), sufficiency |
| EGA | IV 17.2.3 | `KaehlerDifferential.exists_retraction_mapBaseChange` | (ii), affine case |
| EGA | 0 20.7.3 | `KaehlerDifferential.exists_retraction_mapBaseChange` | discrete case, necessity |
| EGA | 0 20.7.2 | `KaehlerDifferential.exists_retraction_mapBaseChange` | sufficiency |
| SGA | 1 II 4.3 | `KaehlerDifferential.exists_retraction_mapBaseChange` | (i) inj., affine case |
| SGA | 1 II 4.4 | `KaehlerDifferential.exists_retraction_mapBaseChange` | special case |
| SGA | 6 VIII 2.6 | `KaehlerDifferential.exists_retraction_mapBaseChange` | partial |
| SGA | 3 III 0.12 | `KaehlerDifferential.tensorKaehlerEquivBase` | special case |
| SGA | 3 III 4.8 | `KaehlerDifferential.tensorKaehlerEquivBase` | (iii), special case |
| SGA | 3 VIA 1.3.2 | `KaehlerDifferential.tensorKaehlerEquivBase` | Differentials clause |
| SGA | 5 III 6.9 | `KaehlerDifferential.tensorKaehlerEquivBase` | special case |
| SGA | 7 VI 5.5 | `KaehlerDifferential.tensorKaehlerEquivBase` | special case |
| EGA | 0 21.3.6 | `KaehlerDifferential.tensorKaehlerEquivBase` | partial |
| EGA | 0 22.4.4.7 | `KaehlerDifferential.tensorKaehlerEquivBase` | more general |
| EGA | 0 22.4.8 | `KaehlerDifferential.tensorKaehlerEquivBase` | more general |
| EGA | IV 16.4.5 | `KaehlerDifferential.tensorKaehlerEquivBase` | special case |
| EGA | IV 16.5.10 | `KaehlerDifferential.tensorKaehlerEquivBase` | (16.5.10.1) affine case |
| EGA | 0 20.5.5 | `KaehlerDifferential.tensorKaehlerEquiv` |  |
| EGA | 0 21.3.6 | `KaehlerDifferential.tensorKaehlerEquiv` | partial |
| EGA | 0 22.4.4.7 | `KaehlerDifferential.tensorKaehlerEquiv` | more general |
| EGA | 0 22.4.8 | `KaehlerDifferential.tensorKaehlerEquiv` | more general |
| EGA | IV 16.5.10 | `KaehlerDifferential.tensorKaehlerEquiv` | (16.5.10.1) affine case |
| EGA | 0 20.5.5 | `KaehlerDifferential.tensorKaehlerEquivBase` |  |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/Kaehler/BaseChange.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 5 declarations of the source file 3 are kept. The 2 left out are not needed by the results for which the extract is made: `omega_localization_base`, `omega_localization_total`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 23 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
