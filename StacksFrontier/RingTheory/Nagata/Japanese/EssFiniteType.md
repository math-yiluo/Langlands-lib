# N-2 read on an arbitrary fraction field

Module `StacksFrontier.RingTheory.Nagata.Japanese.EssFiniteType`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

`isN2_apply_of_isFractionRing` applies the N-2 condition with an arbitrary fraction field. If a domain `S₀` satisfies `IsN2_032s S₀`, which is phrased with `FractionRing S₀`, and `K` is any field with `IsFractionRing S₀ K`, then for every finite extension `L` of `K`, with a compatible tower `S₀ → K → L`, the integral closure of `S₀` in `L` is a finite `S₀`-module. The proof transports the algebra structures along the canonical isomorphism `FractionRing S₀ ≃ₐ[S₀] K`, so that `L` becomes a finite extension of `FractionRing S₀`, and applies the hypothesis. All rings and fields lie in one universe.

The module docstring still announces that an algebra essentially of finite type over a universally Japanese ring is universally Japanese (Tag 032S), and a long comment before the lemma describes the core step of that proof; neither result is in the file.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/Nagata/Japanese/EssFiniteType.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 8 declarations of the source file 1 are kept. The 7 left out are not needed by the results for which the extract is made: `algebraMap_ne_zero_of_le_nonZeroDivisors`, `essFiniteType_of_isEssentiallyOfFiniteType`, `isFractionRing_of_localization_aux`, `isN2_of_essFiniteType_of_universallyJapanese`, `isN2_of_isLocalization`, `isUniversallyJapanese_of_isEssentiallyOfFiniteType`, `module_finite_integralClosure_localization`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
