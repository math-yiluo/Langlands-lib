# Conditional below-break norm coordinate assembly

Author: Worker 96.

This internal support module proves the positive below-break coordinate clause
conditionally on proofs of `PrimeRamifiedTraceIdeals` and
`PrimeNormTraceExpansion`. Those two propositions remain explicit proof
parameters; this module proves neither arithmetic input nor the closed
`PrimeRamifiedGradedNorm` target.

`coordinate_of_expansion` works for any finite extension with the supplied
scalar structures. Given integral witnesses for the three divided terms of
an actual norm expansion, it divides the expansion by the supplied target
uniformizer power and applies the residue homomorphisms. The target unit
coefficient is therefore the sum of the three residue contributions.

`below_break_of_arithmetic` assumes prime relative degree, Galoisness, total
ramification, the supplied lower-group pattern, and `0 < n < t`. It constructs
the actual nonzero norm coefficient using `norm_coefficient`, retaining the
literal field value `N(piL)^n / piF^n`. For `delta = x - 1`, the two arithmetic
proof parameters give integral trace witnesses for `delta` and the expansion
remainder, whose source ideal exponents are respectively `n` and `2*n`.
The inequality

`n + 1 <= ((t + 1) * (ell - 1) + n) / ell`

puts both trace witnesses in the next target ideal power. Their quotients by
`piF^n` consequently have zero residue. Applying `coordinate_of_expansion`
leaves the norm contribution. The existing `norm_term_coordinate` computes
that contribution, and the positive ramification break identifies `ell` with
`p`. This yields exactly the below-break coordinate formula for every pair of
source and target filtration representatives related by the actual unit norm.
Both supplied uniformizers and the actual forward relative residue map are
retained. The independent field universes are unrestricted.

The provenance is an internal assembly of the imported quotient, norm and
filtration support. The mathematical route is the below-break calculation in
Serre, *Local Fields* (1979), Chapter V, section 3, Proposition 5, printed
pages 84–85 (PDF pages 91–92), especially case (ii) on page 85. The registered
2019 author corrections, PDF pages 2–3, list no correction to this passage.
The conditional scope is narrower than the complete source proposition.

`primeGradedNormBelowBreakFromArithmetic` packages the preceding result with
exact type `PrimeGradedNormBelowBreakFromArithmetic.{u,v}`. It introduces all
quantifiers and applies the implemented below-break proof without further
hypotheses. The arithmetic propositions remain inside this conditional target.

The final theorem explicitly binds its universes in the order `u, v`, matching
the published statement and preserving the two independent field universes.
