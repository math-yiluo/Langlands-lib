# Minimal primes, zero divisors and reduced rings

Module `StacksFrontier.RingTheory.MinimalPrimes.Reduced`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

This file describes the localizations at minimal primes and uses them to embed a reduced commutative ring into the product of its localizations at minimal primes, which are fields, and to compute its zero divisors.

- `localizationProdMap` is the product of the localization maps at all minimal primes. For a reduced commutative ring, `localizationProdMap_injective` proves injectivity and `isField_localizationAtPrime_of_minimal` shows that each factor is a field; `minimal_prime_reduced_localization_isField` records the same field conclusion, with the primality of p as an instance argument.
- `iUnion_minimalPrimes_eq_zeroDivisors` says that for a reduced commutative ring the union of the minimal primes is `zeroDivisorSet`, defined using a nonzero element annihilated by the given element.

The localization at a minimal prime has Krull dimension at most zero. The lemma `nilradical_eq_sInf_minimalPrimes` identifies the intersection of the minimal primes with the nilradical, which vanishes in the reduced case. There the kernel of each localization is its corresponding minimal prime.

The definitions, the Krull-dimension bound and the nilradical lemma apply to commutative semirings. The embedding and zero-divisor equality are stated for reduced commutative rings. The module docstring still announces an embedding into a product of fields as a theorem of its own, a basic open separating a minimal prime from a quasi-compact open, and the nilpotence of the maximal ideal of the localization at a minimal prime; none of these is in the file.

The Stacks attributes cite Tag 00EW; the module docstring also lists Tag 00EV and Tag 00EU. The references for the nilradical, local dimension and reduced-ring statements are EGA 0 1.1.1, EGA 0 1.5.8, EGA I 7.1.5 and EGA IV 20.1.3.1.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [00EW](https://stacks.math.columbia.edu/tag/00EW) | `isField_localizationAtPrime_of_minimal` | 2, the factors are fields |
| [00EW](https://stacks.math.columbia.edu/tag/00EW) | `localizationProdMap_injective` | 2, injectivity; the factors are fields by isField_localizationAtPrime_of_minimal |
| [00EW](https://stacks.math.columbia.edu/tag/00EW) | `iUnion_minimalPrimes_eq_zeroDivisors` | 3 |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | 0 1.1.1 | `nilradical_eq_sInf_minimalPrimes` | Case a = (0) |
| EGA | 0 1.1.1 | `sInf_minimalPrimes_eq_bot` | special case |
| EGA | IV 20.1.3.1 | `sInf_minimalPrimes_eq_bot` | partial |
| EGA | IV 20.1.3.1 | `eq_zero_iff_mem_all_minimalPrimes` | affine zero detection |
| EGA | 0 1.5.8 | `krullDimLE_localization_atPrime_minimal` | more general |
| EGA | I 7.1.5 | `krullDimLE_localization_atPrime_minimal` | special case |
| EGA | 0 1.5.8 | `isField_localizationAtPrime_of_minimal` | reduced ring |
| EGA | IV 20.1.3.1 | `isField_localizationAtPrime_of_minimal` | field-stalk clause |
| EGA | IV 20.1.3.1 | `mem_minimalPrime_imp_zeroDivisor` | converse direction |
| EGA | IV 20.1.3.1 | `zeroDivisor_imp_mem_minimalPrime` | partial, special case |
| EGA | IV 20.1.3.1 | `iUnion_minimalPrimes_eq_zeroDivisors` | special case |
| EGA | 0 1.5.8 | `minimal_prime_reduced_localization_isField` | reduced ring |
| EGA | IV 20.1.3.1 | `minimal_prime_reduced_localization_isField` | partial |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/MinimalPrimes/Reduced.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 24 declarations of the source file 17 are kept. The 7 left out are not needed by the results for which the extract is made: `PrimeSpectrum.exists_disjoint_basicOpen_of_mem_minimalPrimes`, `compact_open_eq_finset_basicOpens`, `exists_basicOpen_subset_of_mem_open`, `exists_disjoint_basicOpen_finset`, `exists_injective_ringHom_pi_field`, `exists_mul_pow_eq_zero_of_mem_minimalPrimes`, `minimal_prime_maximalIdeal_isNilpotent`.
- 1 command that is not a declaration is left out or changed with the declarations left out (`notes/reuse/stacks-extract/extract-commands.tsv.md`).
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 13 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
