# Minimal-prime decompositions for affine normalization

Module `StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.TotalFractionRing`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

The affine computation of normalization for a reduced scheme uses two product decompositions, one for the total fraction ring and one for the integral closure inside it.

- `AlgebraicGeometry.finite_minimalPrimes_of_affine_open` assumes that each quasi-compact open of X has finitely many irreducible components. If an open subscheme of X is isomorphic to Spec A, then A has finitely many minimal primes. The proof transports irreducible components through the affine isomorphism and uses their correspondence with minimal primes.
- `minimalPrimes.totalFractionRing_algEquiv_pi_fractionRing_quotient` gives an A-algebra equivalence from the total fraction ring of a reduced ring A with finitely many minimal primes to the product of the fraction fields of A/p over those primes.
- `minimalPrimes.integralClosure_fractionRing_algEquiv_pi_quotient` under the same hypotheses gives an A-algebra equivalence from the integral closure of A in its total fraction ring to the product of the integral closures of A/p in their fraction fields.

The fraction-ring proof realizes the product of the localizations at the minimal primes as the localization at the non-zero-divisors. Each factor is the fraction field of the corresponding quotient. The integral-closure proof then uses coordinatewise integrality in a finite product and compares integrality over A with integrality over each quotient.

The last two results assert existence of algebra equivalences, with the factors carrying the A-action through the quotient maps. The first result applies to arbitrary schemes satisfying the component-finiteness condition. The tagged declarations supply the minimal-prime and ring-theoretic parts of the affine normalization computation.

Stacks Project, Tag 035P. EGA II 6.3.6, II 6.4.7 and II 6.5.1.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [035P](https://stacks.math.columbia.edu/tag/035P) | `finite_minimalPrimes_of_affine_open` | minimal_primes |
| [035P](https://stacks.math.columbia.edu/tag/035P) | `totalFractionRing_algEquiv_pi_fractionRing_quotient` | total_fraction_ring |
| [035P](https://stacks.math.columbia.edu/tag/035P) | `integralClosure_fractionRing_algEquiv_pi_quotient` | integral_closure_product |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | II 6.5.1 | `totalFractionRing_algEquiv_pi_fractionRing_quotient` | partial |
| EGA | II 6.3.6 | `integralClosurePiEquiv` | special case |
| EGA | II 6.4.7 | `integralClosurePiEquiv` | more general |
| EGA | II 6.4.7 | `integralClosure_fractionRing_algEquiv_pi_quotient` | integral closure product |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Morphisms/Normalization/TotalFractionRing.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 4 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
