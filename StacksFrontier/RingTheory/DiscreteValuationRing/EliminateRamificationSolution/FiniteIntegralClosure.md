# Elimination of ramification from Epp's theorem, part 5: finite integral closures and finite stages

Module `StacksFrontier.RingTheory.DiscreteValuationRing.EliminateRamificationSolution.FiniteIntegralClosure`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

This is part 5 of the library's derivation of Tag 09II from Epp's theorem (Tag 09F9). It proves finiteness of integral closures over discrete valuation rings and Dedekind domains when the generic algebra is geometrically reduced, shows that primes and nilradicals over an algebraic extension E/K already appear over a finite subextension, and finds finite extensions after which reduced tensor products become geometrically reduced.

## Main results

- `finite_integralClosure_localization_of_isDedekindDomain`: let R be a Dedekind domain with fraction field K, S essentially of finite type over R, T essentially of finite type over S and geometrically reduced as a K-algebra. For a prime q of S over a nonzero prime of R, the integral closure of S_q in the localization of T at q is finite over S_q.
- `finite_integralClosure_of_isLocalized_maximal`: over a ring with finitely many maximal ideals, finiteness of an integral closure can be checked after localizing at each maximal ideal.
- `exists_primeSpectrum_bijective_integralClosure_reducedTensor_finite_stage`: for E/K algebraic, if the integral closure C of B in (L ⊗_K E)_red is Noetherian with finite spectrum, there is a finite subextension F such that, for every finite G ⊇ F, the map from the integral closure at stage G to C is bijective on spectra and every prime of C is extended from stage G. `exists_primeSpectrum_bijective_integralClosureMap_finite_stage` does the same for the integral closure of A in E.
- `exists_finite_intermediateField_nilradical_map_eq`: for E/K algebraic, a finitely generated nilradical of A ⊗_K E is extended from A ⊗_K F for some finite F.
- `exists_finite_extension_isGeometricallyReduced_reducedTensorProduct`: for A essentially of finite type over K and any E/K, some finite F/E makes (A ⊗_K F)_red geometrically reduced over F.
- `isSeparableExtension_of_injective_tensorProduct`: if E ⊗_K L embeds into a separable extension of E, then L/K is separable.
- `map_maximalIdeal_localRingHom_of_map_comap_eq` and `integralClosureReducedTensorMap` support the finite stages.

## Proofs

The Dedekind case reduces to a discrete valuation ring by localizing. There the completion is faithfully flat, reduced and Nagata, an essentially finite type algebra over a Nagata ring is Nagata, geometric reducedness keeps the base change reduced, and finiteness of the integral closure descends. Finite stages come from directed unions of finite subextensions and finite generation of ideals.

## Points to watch

- The two spectrum-bijection results take Noetherianity and finite spectrum of the integral closures as hypotheses.
- Geometric reducedness of the generic algebra is a hypothesis of the Dedekind-domain and discrete-valuation-ring finiteness results.
- The private finiteness lemma over a discrete valuation ring is attached to EGA II, 6.3.10, marked as a partial special case.

## References

Tag 09II, Tag 09F9; EGA II, 6.3.10 (partial, special case).

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | II 6.3.10 | `finite_integralClosure_of_isDiscreteValuationRing_of_isGeometricallyReduced` | partial, special case |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/DiscreteValuationRing/EliminateRamificationSolution/FiniteIntegralClosure.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- One reference to EGA or SGA, written in the source as an attribute of that library, is taken out of the Lean text and listed above.
