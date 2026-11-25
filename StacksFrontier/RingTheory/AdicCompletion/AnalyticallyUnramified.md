# Discrete valuation localizations after completion

Module `StacksFrontier.RingTheory.AdicCompletion.AnalyticallyUnramified`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Let R be a commutative Noetherian local ring and let R̂ be its maximal-ideal completion. The file gives a criterion for a localization of R̂ to be a discrete valuation ring.

`mCompletion` denotes R̂ and `pCompletion` extends an ideal p to R̂. The predicate `AnalyticallyUnramifiedPrime` means that R̂/pR̂ is reduced. It is defined for any ideal p, with primality supplied separately in the main theorem.

`exists_isDiscreteValuationRing_atPrime_of_analyticallyUnramified` assumes p is prime, Rₚ is a domain with a discrete valuation ring structure, and `hunr` asserts that p is analytically unramified. For each associated prime q of R̂/pR̂ as an R̂-module, it supplies proofs of primality of q and of the domain and discrete valuation ring properties of R̂ localized at q. The associated-prime predicate is expressed using the radical of an element annihilator.

Reducedness makes q minimal over pR̂ and identifies the maximal ideal after localization with the extension of p. Flat going-down shows that q contracts to p, and the faithfully flat local map from Rₚ to the localized completion carries a uniformizer to a nonnilpotent generator of its maximal ideal. The Krull intersection argument in `regular_of_principal_maximalIdeal_of_not_nilpotent` makes that generator a nonzerodivisor in the localized completion, giving the discrete valuation ring criterion. The proof sketch in the file describes that step through faithful flatness of R → R̂ and refers to a lemma L4, which the file does not contain.

## Noetherianity input

`mCompletion_isNoetherianRing` proves Noetherianity for the maximal-ideal completion of a Noetherian local ring. Given finitely many generators of an ideal, `Stacks.NoetherianCompletion.Φ` evaluates power series at them by compatible quotient evaluations. The proof of `Stacks.NoetherianCompletion.Φ_surjective` lifts a compatible residue family by correcting its representatives with monomials of successively higher degree. The power series ring is Noetherian by `mvPowerSeries_fin_isNoetherianRing`, from the imported module `StacksFrontier.RingTheory.MvPowerSeries.Noetherian`.

## References

The valuation result is Tag 032Z. The Noetherianity input is the maximal-ideal case of Tag 0316.

For completion and its Noetherianity, see EGA 0 7.3.1, EGA 0 7.6.11, EGA 0 10.2.3, EGA 0 17.3.8.1, EGA 0 19.8.3, EGA I 10.6.4, EGA II 8.10.3, EGA III 7.5.1, EGA IV 8.11.4, SGA 1 II 4.14, SGA 1 IV 3.1, SGA 3 VIIB 2.6, SGA 3 VIIB 4.1.1, SGA 3 VIIB 5.5.2, SGA 3 X 4.0, and SGA 7 VI 4.1(d). The references for ramification, associated primes, and the local criterion include SGA 1 I 9.4, EGA IV 3.2.1, SGA 2 IV 5.3, EGA 0 17.1.4, EGA II 7.1.6, EGA III 7.6.3, EGA IV 14.5.7, EGA IV 3.4.1, EGA IV 3.4.1.2, and EGA IV 5.12.7.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [032Z](https://stacks.math.columbia.edu/tag/032Z) | `exists_isDiscreteValuationRing_atPrime_of_analyticallyUnramified` |  |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | 0 10.2.3 | `mCompletion` | special case |
| EGA | 0 17.3.8.1 | `mCompletion` | special case |
| EGA | 0 19.8.3 | `mCompletion` |  |
| EGA | 0 7.3.1 | `mCompletion` | special case |
| EGA | II 8.10.3 | `mCompletion` |  |
| EGA | III 7.5.1 | `mCompletion` | Â, special case |
| EGA | IV 8.11.4 | `mCompletion` |  |
| SGA | 1 II 4.14 | `mCompletion` | special case |
| SGA | 1 IV 3.1 | `mCompletion` | maximal-ideal completion |
| SGA | 3 VIIB 2.6 | `mCompletion` | partial |
| SGA | 3 VIIB 4.1.1 | `mCompletion` | partial |
| SGA | 3 X 4.0 | `mCompletion` |  |
| SGA | 7 VI 4.1(d) | `mCompletion` |  |
| SGA | 1 I 9.4 | `AnalyticallyUnramifiedPrime` | more general |
| EGA | IV 3.2.1 | `assoc_prime_mem_minimalPrimes_of_isReduced` | partial |
| SGA | 2 IV 5.3 | `regular_of_principal_maximalIdeal_of_not_nilpotent` | case n = 1 |
| EGA | 0 17.1.4 | `l5_assemble` | partial |
| EGA | II 7.1.6 | `l5_assemble` | regular ⇒ DVR |
| EGA | III 7.6.3 | `l5_assemble` | Local implication |
| EGA | IV 14.5.7 | `l5_assemble` | more general |
| EGA | IV 3.4.1 | `l5_assemble` | (iii) |
| EGA | IV 3.4.1.2 | `l5_assemble` | Parenthetical in β |
| EGA | IV 5.12.7 | `l5_assemble` | special case |
| EGA | 0 7.3.1 | `mCompletion_isNoetherianRing` | special case |
| EGA | 0 7.6.11 | `mCompletion_isNoetherianRing` | (ii), special case |
| EGA | I 10.6.4 | `mCompletion_isNoetherianRing` | special case |
| EGA | IV 8.11.4 | `mCompletion_isNoetherianRing` | Â is Noetherian |
| SGA | 3 VIIB 5.5.2 | `mCompletion_isNoetherianRing` | Noetherianity of Â |
| SGA | 3 X 4.0 | `mCompletion_isNoetherianRing` | partial |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/AdicCompletion/AnalyticallyUnramified.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 52 declarations of the source file 47 are kept. The 5 left out are not needed by the results for which the extract is made: `Stacks.NoetherianCompletion.mvps_bij_sum`, `Stacks.NoetherianCompletion.mvps_emptyEquiv`, `Stacks.NoetherianCompletion.mvps_stepEquiv`, `Stacks.NoetherianCompletion.mvps_sumCurry`, `l4_nonzerodivisor`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 29 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
