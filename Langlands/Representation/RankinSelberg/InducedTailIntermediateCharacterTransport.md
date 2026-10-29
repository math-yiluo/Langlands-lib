# Inverse-character transport for the intermediate tail

Supporting module written by Worker 318 and submitted by Worker 968 with the
proof of `InducedTailIntermediateInverseCharacterStatement`. This module
derives the special case of the published actual character-change construction
at the field unit `-1`. It is internal infrastructure for the character issue
identified in JPSS section 9.3, printed 456–457. It does not prove the
intermediate-tail inclusion or its localization.

`characterChangeElement_neg_one_abs_det` shows that the determinant of the
actual character-change diagonal has absolute value one. The quotient modulus
`characterChangeModulus_neg_one` is imported from `EqualRankSwapTransport`.
This module proves that the rectangular modulus, a power of `|-1| = 1`, is
also one. The determinant half-gap factor is a power of the same absolute
value. Therefore `unequalRankCharacterChangeScalar_neg_one` shows that the
published unequal-rank character-change scalar is the unit one, and the
spectral exponent can be taken to be zero. The pointwise identity
`scaled_neg_one_apply`, `ψ.scale (-1) x = (ψ x)⁻¹`, records the reversal
explicitly. It follows from `AddChar.map_neg_eq_inv`.

Under the published quotient and rectangular measure laws, the module specializes
the actual integral and rational-value transports. These are
`unequalRankIntegral_characterChange`,
`unequalRankConverges_characterChange_iff`,
`unequalRankZetaValues_characterChange` and
`unequalRankZetaValues_characterChange_reverse`. The two value-set transports
carry the coefficient-image witnesses forward and back, together with the
product-integrability equivalence and the rational continuation. With scalar
one and exponent zero, `unequalRankZetaValues_scale_neg_one` therefore proves
equality of actual value sets, not only equality of Laurent spans. No analytic
continuation existence or integral comparison is assumed beyond membership in
the actual value set.

The general part retains an arbitrary field universe and independent
representation universes, any positive residue parameter, all row/gap indices,
and arbitrary measures satisfying those two explicit change laws. The direct
integral identity uses neither a residue parameter nor sigma finiteness.
The absolute convergence equivalence uses the published product-measure
transport with sigma-finite measures. The continuation equivalence follows by
extensional equality of the actual integral functions and retains the identical
rational function.

The two compatible-measure specializations,
`unequalRankZetaValues_scale_neg_one_compatible` and
`unequalRankZetaValuesAt_scale_neg_one_compatible`, use the supplied p-adic
topological realization and any additive Haar measure. They identify each of the two
independently supplied compatible quotient measures with the canonical quotient
measure by `unipotentQuotientHaar_unique`. The quotient character-change law,
canonical quotient sigma finiteness and rectangular product law are discharged
by the published `unipotentQuotientHaar_characterChange`,
`unipotentQuotientHaar_sigmaFinite_normalized` and
`characterChangeRectangularProductStatement`. The p-adic residue cardinality is
positive. These steps prove equality of actual rational zeta-value sets at the
original and inverse characters, with no assumed integral comparison and no
unknown measure scalar. The fixed-large-rank variant substitutes the rank
equation to recover the original definition; it does not change entries or
representations.

This is derived infrastructure using the published character-change proofs,
not a new assertion quoted from JPSS. It addresses the character reversal in
section 9.3 of the registered source `jpss-1983-rankin-selberg`, printed 456–457,
retained as `/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`,
SHA-256 `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
The rendered printed pages 455–457 were checked. In the intermediate case
`r₂ < t < r`, the source rewrites `Ψ(s, W, W'; 0)` as `Ψ(s, W', W₂; 0)`.
Here `W'` lies in the `ψ̄`-Whittaker model of `σ`. This exchange of the two
model characters is the reversal treated here. This module does not
establish a different-rank quotient integration formula, compact-localization
volume, extension theorem or the final intermediate-tail span inclusion.
