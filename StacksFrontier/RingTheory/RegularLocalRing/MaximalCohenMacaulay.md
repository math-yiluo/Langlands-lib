# Freeness of maximal Cohen–Macaulay modules

Module `StacksFrontier.RingTheory.RegularLocalRing.MaximalCohenMacaulay`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Over a regular local ring R, a nonzero finite maximal Cohen–Macaulay module M is free. The file proves this by reducing to a quotient by a parameter and develops the regular-sequence results needed for that reduction.

## Main results

- `IsMaxCM R M` asks for an M-regular list in the maximal ideal of length dim R.
- `regular_mcm_free` gives freeness for nonzero finite M over regular local R under `IsMaxCM R M`. For x in the maximal ideal outside its square, `quotient_isRegularLocalRing` gives regularity of R/(x) and an exact dimension drop of one. If x is also M-regular, `mcm_of_quotient` preserves finiteness, nontriviality and the sequence condition over R/(x), taking the local ring instance on the quotient as an argument.
- `free_of_quotSMulTop_free` lifts freeness of M/xM over R/(x) to freeness of M for finite M over Noetherian local R and an M-regular x in the maximal ideal. It lifts a basis, uses Nakayama for generation and Krull intersection for independence.
- For a finite module over a Noetherian local ring, `rees_length_le_of_maximalIdeal_mem_associatedPrimes_quotient` bounds the length of any M-regular list in the maximal ideal by the length of one whose quotient has the maximal ideal as an associated prime. For nonzero M, `exists_smulRegular_of_lt_length_isRegular` uses the inequality to extend a sequence that is shorter than another regular sequence in the maximal ideal.

The freeness proof inducts on dimension, using `isDomain_of_isRegularLocalRing_aux` for the domain input to the field case. In positive dimension it chooses an M-regular parameter by avoiding associated primes, extends it to a full length sequence using prime avoidance and the Rees inequality, and lifts freeness after induction on the quotient.

The freeness theorem takes the library’s sequence predicate `IsMaxCM` and explicitly assumes `Nontrivial M` and `Module.Finite R M`. The Rees length inequality expresses maximality of the comparison sequence through the associated-prime hypothesis `hmass`. The first module docstring, on lifting freeness modulo a nonzerodivisor, and the last, on the depth form `Module.IsMaximalCohenMacaulay`, announce results that are not in the file; the lifting result here is `free_of_quotSMulTop_free`.

## References

Stacks Project Tag 00NT for freeness and Tag 00NS for lifting it. Tag 00NP concerns the domain result and Tag 00LE attainment of depth. Bruns–Herzog, *Cohen–Macaulay Rings*, Theorem 1.2.5, for exchange. EGA IV, 7.5.3, for the sequence condition. EGA 0, 17.3.5 (i), and EGA IV, 6.1.5, for freeness. EGA 0, 10.1.2 and 10.2.2, and SGA 1, IV, 4.1 (b), for lifting. SGA 2, III, 2.6, for the local Rees inequality.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [00NT](https://stacks.math.columbia.edu/tag/00NT) | `regular_mcm_free` |  |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | IV 7.5.3 | `IsMaxCM` |  |
| EGA | 0 16.3.4 | `ringKrullDim_le_quotient_span_singleton_succ` | special case |
| EGA | 0 16.3.7 | `ringKrullDim_le_quotient_span_singleton_succ` | Local ring; M = A; k = 1 |
| EGA | IV 5.5.1 | `ringKrullDim_le_quotient_span_singleton_succ` | special case |
| EGA | IV 5.5.2 | `ringKrullDim_le_quotient_span_singleton_succ` | special case |
| EGA | 0 16.1.2 | `quotient_regular_of_param_avoiding_minimalPrimes` | special case |
| EGA | 0 16.2.3.1 | `quotient_regular_of_param_avoiding_minimalPrimes` | (ii), special case |
| EGA | 0 16.3.4 | `quotient_regular_of_param_avoiding_minimalPrimes` | special case |
| EGA | 0 17.1.7 | `quotient_regular_of_param_avoiding_minimalPrimes` | r=1: a'⇒b |
| EGA | 0 17.1.9 | `quotient_regular_of_param_avoiding_minimalPrimes` | (b) ⇒ (a), one generator |
| EGA | 0 17.1.3 | `isDomain_of_isRegularLocalRing_aux` |  |
| EGA | 0 17.3.5 | `free_of_isRegularLocalRing_dim_zero` | (i), special case |
| EGA | 0 16.1.2 | `quotient_isRegularLocalRing` | special case |
| EGA | 0 16.2.3.1 | `quotient_isRegularLocalRing` | (ii), special case |
| EGA | 0 16.3.4 | `quotient_isRegularLocalRing` | special case |
| EGA | 0 17.1.7 | `quotient_isRegularLocalRing` | r=1: a'⇒b |
| EGA | 0 17.1.8 | `quotient_isRegularLocalRing` | b ⇒ a |
| EGA | 0 17.1.9 | `quotient_isRegularLocalRing` | (b) ⇒ (a), one generator |
| EGA | IV 5.5.1 | `quotient_isRegularLocalRing` | DVR base, special case |
| SGA | 2 III 2.1 | `notMem_associatedPrimes_of_isSMulRegular` | (iv) ⇒ (v) |
| EGA | 0 16.4.2 | `notMem_associatedPrimes_take_of_isRegular` | sufficiency |
| SGA | 3 V 4.1 | `exists_mem_maximalIdeal_notMem_biUnion` | local ring, special case |
| EGA | IV 3.1.9 | `isSMulRegular_of_forall_notMem_associatedPrimes` | sufficiency direction |
| SGA | 2 III 2.1 | `isSMulRegular_of_forall_notMem_associatedPrimes` | (ii) ⇒ (iv) |
| SGA | 3 V 7.2 | `isSMulRegular_of_forall_notMem_associatedPrimes` | partial |
| EGA | 0 16.4.4 | `rees_length_le_aux` | more general |
| EGA | 0 16.4.6 | `rees_length_le_aux` | (i) |
| EGA | 0 16.4.4 | `rees_length_le_of_maximalIdeal_mem_associatedPrimes_quotient` | more general |
| SGA | 2 III 2.6 | `rees_length_le_of_maximalIdeal_mem_associatedPrimes_quotient` | Local case |
| EGA | 0 1.7.5 | `ofList_smul_top_ne_top_of_le_maximalIdeal` | Nakayama step: mM ≠ M |
| EGA | 0 7.1.13 | `ofList_smul_top_ne_top_of_le_maximalIdeal` | local ring, special case |
| EGA | IV 2.5.5.4 | `ofList_smul_top_ne_top_of_le_maximalIdeal` | more general |
| EGA | 0 10.1.2 | `free_of_quotSMulTop_free` | special case |
| EGA | 0 10.2.2 | `free_of_quotSMulTop_free` | (x), special case |
| SGA | 1 IV 4.1 | `free_of_quotSMulTop_free` | (b), special case |
| EGA | 0 17.3.5 | `regular_mcm_free_aux` | (i), sufficiency |
| EGA | 0 17.3.5 | `regular_mcm_free` | (i), sufficiency |
| EGA | IV 6.1.5 | `regular_mcm_free` | special case |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/RegularLocalRing/MaximalCohenMacaulay.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 47 declarations of the source file 41 are kept. The 6 left out are not needed by the results for which the extract is made: `exchange_isSMulRegular_quotSMulTop`, `exists_isRegular_length_eq_ringKrullDim_of_isMaximalCohenMacaulay`, `exists_isSMulRegular_two`, `free_mod_x`, `isMaximalCohenMacaulay_of_exists_isRegular`, `rees_length_le_one_of_maximalIdeal_mem_quotSMulTop`.
- 2 commands that are not declarations are left out or changed with the declarations left out (`notes/reuse/stacks-extract/extract-commands.tsv.md`).
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 38 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
