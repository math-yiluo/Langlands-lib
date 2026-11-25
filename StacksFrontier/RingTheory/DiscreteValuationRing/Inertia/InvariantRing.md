# The inertia-invariant ring and its residue extension

Module `StacksFrontier.RingTheory.DiscreteValuationRing.Inertia.InvariantRing`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Let A be a discrete valuation ring with fraction field K, let L/K be finite Galois, and let B be the integral closure of A in L. For a maximal ideal P of B, let I be its inertia group, C the invariant subalgebra of B, and q the contraction of P to C.

`inertia_fixedSubalgebra_isIntegralClosure_and_etale_localization` identifies C as the integral closure of A in the fixed field of I and proves that C localized at q is étale over A. The general helper `etale_atPrime_of_ramificationIdx_eq_one` obtains étaleness at a maximal ideal of a finite flat algebra over a noetherian ring, assuming finite prime spectrum upstairs, index one and a separable residue extension. For a finite flat extension of domains with a finite Galois group G, `card_stabilizer_eq_ramificationIdx_mul_inertiaDeg` gives the order of the decomposition group at a prime as ef; `finite_primeSpectrum_of_isDiscreteValuationRing` records that a DVR has finitely many primes.

The integral-closure identification restricts the embedding into L to elements fixed by I. The decomposition-group order formula, the residue automorphism quotient and the tower formulas give index one and residue separability at q; above C the full group is inertia, so the separable residue degree there is one. Finite spectrum makes localization at q a localization away from one element, which supplies finite presentation.

The module docstring also states that the residue extension above C is purely inseparable; the file has no such theorem.

References include Tag 09EH and the partial correspondence with SGA 7 I 0.3.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [09EH](https://stacks.math.columbia.edu/tag/09EH) | `inertia_fixedSubalgebra_isIntegralClosure_and_etale_localization` |  |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| SGA | 7 I 0.3 | `ramificationIdx_eq_one_and_isSeparable_of_inertia` | partial |
| SGA | 7 I 0.3 | `inertia_fixedSubalgebra_isIntegralClosure_and_etale_localization` | partial |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/DiscreteValuationRing/Inertia/InvariantRing.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 9 declarations of the source file 8 are kept. The 1 left out are not needed by the results for which the extract is made: `IsDiscreteValuationRing.inertia_fixedSubalgebra_residue_purelyInseparable`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 2 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
