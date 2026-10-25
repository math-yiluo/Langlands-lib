# Conditional below-break prime graded norm statement

Author: Worker 96.

`PrimeGradedNormBelowBreakFromArithmetic` is an internal proposition isolating
the below-break clause of the existing `PrimeRamifiedGradedNorm` target under
explicit proofs of `PrimeRamifiedTraceIdeals` and `PrimeNormTraceExpansion`.
It retains independent universes for the two p-adic fields, the supplied
algebra and scalar tower, finite dimension, Galoisness, prime relative degree,
total ramification, and the supplied single lower ramification break pattern.

For every pair of supplied order-one uniformizers and every `0 < n < t`, it
requires an integer `a` whose field value is exactly `N(piL)^n / piF^n` and
whose residue is nonzero. For every source and target level-n unit related by
the actual field norm, their literal uniformizer coordinates satisfy

`r(residue(coefficient(y))) = r(residue(a)) * residue(coefficient(x))^p`,

where `r` is the actual forward residue map induced by the supplied algebra.
No identification of the two residue fields is silently installed. The zero,
critical and above-break clauses and filtration containments are outside this
isolated proposition. The arithmetic propositions remain proof hypotheses;
this statement alone establishes none of these results.

The provenance is an internal conditional extraction from the published host
target. The underlying formula is Serre, *Local Fields* (1979), Chapter V,
section 3, Proposition 5, printed pages 84–85 (PDF pages 91–92), case (ii) on
page 85. The 2019 author corrections, PDF pages 2–3, do not correct this passage.
