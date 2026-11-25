# Integral closures of henselian discrete valuation rings

Module `StacksFrontier.RingTheory.DiscreteValuationRing.HenselianIntegralClosure`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Let A be a henselian discrete valuation ring with fraction field K and let E/K be finite. The file establishes the ring and algebra properties of the integral closure C of A in E.

- `isLocalRing_of_finite_of_henselianLocalRing` makes any module-finite domain over a henselian local ring local. The theorem `isLocalRing_of_isIntegral_of_henselianLocalRing` extends this to domains integral over the henselian base, and `isLocalRing_integralClosure` applies it to C.
- `isDiscreteValuationRing_integralClosure` gives the DVR structure on C. Krull–Akizuki, `isDedekindDomain_integralClosure`, makes C a Dedekind domain without henselianness. The helper `isDiscreteValuationRing_of_isIntegral` applies to a local Dedekind domain integral and faithful over a DVR.
- `isFractionRing_integralClosure` identifies E as the fraction field of C. The map A → C is local by `isLocalHom_algebraMap_integralClosure`.
- `isLocalization_integralClosure_of_isIntegral` treats a localization S of R and an integral S-algebra T. It identifies T with the localization of an integral closure of R in T at the image of the original submonoid.

For locality, the henselian decomposition of a finite algebra into a product of local rings has a single factor in a domain. The integral case applies this inside finite simple subalgebras. Krull–Akizuki and locality give the DVR assertion, and the localization argument clears denominators in integral equations.

The module docstring also announces flatness of C over A and, for separable E/K, module finiteness; neither is in the file.

References include Tag 04GJ for the henselian decomposition, Tag 09IG for Krull–Akizuki and Tag 09EM for the base-change setting. The locality results cite EGA IV 18.5.9(ii), EGA 0 23.2.6 and SGA 4 VIII 4.1(i) in the cases stated here. The DVR assertion cites SGA 6 X 7.16.

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | IV 18.5.9 | `isLocalRing_of_finite_of_henselianLocalRing` | (ii), special case |
| SGA | 4 VIII 4.1 | `isLocalRing_of_finite_of_henselianLocalRing` | (i), special case |
| SGA | 4 VIII 4.1 | `isLocalRing_of_isIntegral_of_henselianLocalRing` | (i), special case |
| EGA | 0 23.2.6 | `isLocalRing_integralClosure` | special case |
| SGA | 6 X 7.16 | `isDiscreteValuationRing_integralClosure` | special case |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/DiscreteValuationRing/HenselianIntegralClosure.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 14 declarations of the source file 11 are kept. The 3 left out are not needed by the results for which the extract is made: `Stacks.DiscreteValuationRing.Ramification.flat_integralClosure`, `Stacks.DiscreteValuationRing.Ramification.flat_of_faithfulSMul`, `Stacks.DiscreteValuationRing.Ramification.module_finite_integralClosure`.
- 3 commands that are not declarations are left out or changed with the declarations left out (`notes/reuse/stacks-extract/extract-commands.tsv.md`).
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 5 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
