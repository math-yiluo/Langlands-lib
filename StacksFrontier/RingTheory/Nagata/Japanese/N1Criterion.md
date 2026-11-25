# Integral closures and their fraction fields

Module `StacksFrontier.RingTheory.Nagata.Japanese.N1Criterion`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

The file holds two lemmas about integral closures in fields.

`isFractionRing_integralClosure` takes a domain `A` with fraction field `Fr` and a field `LL` algebraic over `Fr`, with a compatible tower `A → Fr → LL`, and shows that `LL` is a fraction field of the integral closure of `A` in `LL`. The proof makes `LL` algebraic over `A` through `Fr` and applies `integralClosure.isFractionRing_of_algebraic`.

`module_finite_integralClosure_of_isN1` shows that N-1 in the form `StacksIsN1 S`, finiteness of the integral closure of `S` in `FractionRing S`, gives finiteness of the integral closure of `S` in any field `L` with `IsFractionRing S L`: the canonical isomorphism `FractionRing S ≃ₐ[S] L` carries one integral closure onto the other.

The module docstring still announces the criterion of Tag 0351, that a ring over which every finite-type domain is N-1 is universally Japanese; that theorem is not in the file.

The table cites EGA II 6.3.7 and EGA II 6.3.9.

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | II 6.3.7 | `isFractionRing_integralClosure` | special case |
| EGA | II 6.3.9 | `isFractionRing_integralClosure` | special case |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/Nagata/Japanese/N1Criterion.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 8 declarations of the source file 2 are kept. The 6 left out are not needed by the results for which the extract is made: `exists_clearedBasis_spanning`, `exists_integral_smul`, `exists_monic_dvd_coeff_aeval_eq_zero`, `isFractionRing_of_span_eq_top`, `isN2_of_isN1_of_clearedBasis`, `isUniversallyJapanese_of_finiteType_isN1`.
- 2 commands that are not declarations are left out or changed with the declarations left out (`notes/reuse/stacks-extract/extract-commands.tsv.md`).
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 2 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
