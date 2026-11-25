# Galois action on primes and the structure of inertia

Module `StacksFrontier.RingTheory.DiscreteValuationRing.Galois`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Let A be a discrete valuation ring with fraction field K, let L/K be finite Galois, and let B be the integral closure of A in L, with Gal(L/K) acting through `IsIntegralClosure.MulSemiringAction`. The file describes the action on the maximal ideals of B and the inertia and wild inertia groups at a chosen maximal ideal P.

- `galAction_transitive_on_maximalIdeals_integralClosure` gives transitivity. If there are n maximal ideals, `exists_uniform_ramificationIdx_inertiaDeg_and_finrank_eq` gives common positive ramification index e and residue degree f with [L : K] = nef.
- `exists_wildInertia_exact_and_tameInertia_equiv_rootsOfUnity` gives the exact sequence from wild inertia W through the inertia group I = `Ideal.inertia` onto the e-th roots of unity of B/P; the decomposition group D is `MulAction.stabilizer`. The character is determined by the uniformizer ratio, expressed by a congruence modulo P². Its kernel W acts trivially on P/P² and is normal in D. In positive residue characteristic p it is a p-group, and the cyclic quotient has order the prime-to-p part of e. In residue characteristic zero W is trivial and the quotient has order e. For separable residue extensions, W is also the kernel of the D-action on B/P².

Conjugate maximal ideals have the same ramification index and residue degree, so transitivity makes each of the n terms of the sum formula equal to ef, which gives the degree identity. For the character, the base uniformizer factors as a power of a generator of P times an element outside P; `exists_eq_pow_ramificationIdx_mul` proves this for a prime over a principal prime in a principal Dedekind domain. The filtration by powers of P controls the kernel, and the order of I is e times the inseparable residue degree, which uses `finSepDegree_eq_card_aut_of_normal`: a normal field extension has as many automorphisms as its separable degree.

The module docstring also announces results on the decomposition group and the residue extension that the file does not contain.

## References

Tag 09EA, Tag 09EB, Tag 09EC and Tag 09EE. SGA 1 V 6.13 and XIII 2.0. SGA 3 I 2.3.3, VIIB 2.5.A and XXI 6.7.2. SGA 5 IIIB 5.13 and X 4.2. SGA 7 I 0.3 and XIII 0.2.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [09EA](https://stacks.math.columbia.edu/tag/09EA) | `galAction_transitive_on_maximalIdeals_integralClosure` |  |
| [09EB](https://stacks.math.columbia.edu/tag/09EB) | `exists_uniform_ramificationIdx_inertiaDeg_and_finrank_eq` |  |
| [09EE](https://stacks.math.columbia.edu/tag/09EE) | `exists_wildInertia_exact_and_tameInertia_equiv_rootsOfUnity` |  |
| [09EC](https://stacks.math.columbia.edu/tag/09EC) | `MulAction.stabilizer` | (1), the decomposition group |
| [09EC](https://stacks.math.columbia.edu/tag/09EC) | `Ideal.inertia` | (2), the inertia group |
| [09EC](https://stacks.math.columbia.edu/tag/09EC) | `Ideal.Quotient.stabilizerHom` | The action of the decomposition group on the residue algebra |
| [09EC](https://stacks.math.columbia.edu/tag/09EC) | `Ideal.Quotient.ker_stabilizerHom` | The inertia group as the kernel of the residue-algebra action |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| SGA | 1 XIII 2.0 | `exists_wildInertia_exact_and_tameInertia_equiv_rootsOfUnity` | inertia structure |
| SGA | 7 I 0.3 | `exists_wildInertia_exact_and_tameInertia_equiv_rootsOfUnity` | finite Galois case |
| SGA | 1 V 6.13 | `MulAction.stabilizer` |  |
| SGA | 3 I 2.3.3 | `MulAction.stabilizer` | special case |
| SGA | 3 VIIB 2.5.A | `MulAction.stabilizer` |  |
| SGA | 3 XXI 6.7.2 | `MulAction.stabilizer` | more general |
| SGA | 5 IIIB 5.13 | `MulAction.stabilizer` | more general |
| SGA | 5 X 4.2 | `MulAction.stabilizer` |  |
| SGA | 7 I 0.3 | `Ideal.inertia` |  |
| SGA | 7 XIII 0.2 | `Ideal.inertia` |  |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/DiscreteValuationRing/Galois.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 29 declarations of the source file 26 are kept. The 3 left out are not needed by the results for which the extract is made: `IsDiscreteValuationRing.exists_uniformizerRatioMap_to_rootsOfUnity`, `IsDiscreteValuationRing.residueField_normal_and_stabilizerHom_surjective_of_isGalois`, `IsDiscreteValuationRing.under_eq_maximalIdeal_and_ker_stabilizerHom_eq_inertia`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 10 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
