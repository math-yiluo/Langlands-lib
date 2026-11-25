# Criteria for weak solutions of Artin–Schreier layers

Module `StacksFrontier.RingTheory.DiscreteValuationRing.ArtinSchreier.WeakSolutionCriteria`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

This file collects criteria used to eliminate ramification of degree p in an extension of discrete valuation rings A → C with fraction fields K ⊆ M, in characteristic p. A weak solution, in the sense of the library's `IntegralClosureBaseChange.IsWeakSolution`, is a finite extension E/K for which, as the proofs here unfold it, every maximal ideal of the integral closure of C in (M ⊗_K E)_red has ramification index one over the integral closure of A in E. The file reduces this to a statement about field factors.

## Main results

- `isWeaklyUnramified_of_artinSchreier_parameter_integral`: for an extension of discrete valuation rings B → C with fraction fields L, M of characteristic p, if M = L(z) with z^p − z = ξ and ξ comes from B, then B → C is weakly unramified. The degree of M/L is not assumed to be p.
- `exists_isWeakSolution_of_fieldFactor_ramification`: for E/K finite separable, E/K is a weak solution for A → C as soon as, for every discrete valuation ring Q over C whose fraction field F is finite over M and generated over M by the image of a compatible K-embedding ι : E → F, the maximal ideal of Q has ramification index one over the integral closure of A in E. The factors range over the universe `max uM uK`.
- `exists_laurent_numerator_residue_of_unique_max`: if ξ is b plus the sum of aᵢ π^(−eᵢ) over i in s, with e_j > 0 strictly larger than every other exponent, then ξ = π^(−e_j) c with c having the residue of a_j.

Private lemmas cover towers of ramification indices, uniformizers obtained from approximate roots of π, base change of a weakly unramified A → B by a totally ramified E/K, and embeddings of integral closures into discrete valuation rings.

## Proofs

The integral-parameter criterion reads the trivial and unramified alternatives off `isGalois_and_ramification_cases_of_adjoin_root_artinSchreier`. The field-factor reduction rests on `integralClosures_after_finite_fraction_field_extension`.

## Points to watch

- `IsWeaklyUnramified`, `IsWeakSolution`, `IntegralClosureBaseChange`, `IsTotallyRamifiedWithRespectTo` and `ramificationIndex` are the library's own notions.
- In `exists_isWeakSolution_of_fieldFactor_ramification`, E lies in the universe of K.
- The weak solution from a constant parameter and the ramification index p for a pole of order prime to p, which the module docstring announces, are not in the file; the docstring of `exists_isWeakSolution_of_fieldFactor_ramification` also refers to the former.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/DiscreteValuationRing/ArtinSchreier/WeakSolutionCriteria.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 15 declarations of the source file 11 are kept. The 4 left out are not needed by the results for which the extract is made: `IsDiscreteValuationRing.adjoin_range_eq_adjoin_singleton_of_adjoin_eq_top`, `IsDiscreteValuationRing.artinSchreier_sub_sum_pow`, `IsDiscreteValuationRing.isWeakSolution_of_constant_artinSchreier_parameter`, `IsDiscreteValuationRing.ramificationIndex_eq_prime_of_artinSchreier_pole`.
- 1 command that is not a declaration is left out or changed with the declarations left out (`notes/reuse/stacks-extract/extract-commands.tsv.md`).
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
