# Supported Jacquet comparison at every regular positive parameter

Author: Worker 429.

`Langlands.glRelativeRegularComparison` proves the unchanged proposition
`Langlands.GLRelativeRegularComparisonStatement.{uF,uV,uM,uW}`.
For every supported nested fine, middle and coarse Levi datum and every
strictly decreasing real coarse parameter, it constructs a common positive
inner and ambient fine-cuspidal Jacquet multiplicity and proves that the
actual outer standard module has a strong irreducible head.

The field, fine, middle and coarse carrier universes are independent.
The actual ordered block-shape equality and all three supplied support
surjections remain in the statement. The fine twist is
`-v₀ + restrict(t)`, with the original block-size weights in the
positive scalar-root condition. Arbitrary real central shifts and
nongeneric regular parameters are included.

## Tempered induction and the selected branch

The helper `RelativeRegularComparisonProof.unitaryInduced_tempered`
starts from square-integrability modulo the full center of the whole
middle Levi. The published square-integrable-to-tempered theorem gives
analytic temperedness, and `leviImaginaryTwistModCenter` preserves it under
the middle imaginary determinant twist. Character twisting preserves
irreducibility. Choose an actual Borel Haar measure on the middle Levi's
central quotient and apply `glTemperedInductionPreservation` to obtain
analytic temperedness of the actual normalized induction for every
middle unitary parameter. No tensor factorization is assumed.

The helper `ae_occurrence_forces_blockWeyl` receives one fixed permutation,
its actual fine-Levi conjugation witness, its real stabilizer identity,
and almost-everywhere occurrence throughout the middle unitary family.
Lebesgue measure on the finite middle parameter space is nonzero, so
`hae.exists` supplies a parameter at which that same branch occurs.
The code does not specialize an almost-everywhere assertion at zero.

After expanding the exact affine family, the occurring representation is
the transport of the fine datum twisted by `-v₀` plus the imaginary
restriction of the chosen middle parameter. The theorem
`glTemperedOppositeTwistCone`, applied to the tempered induction just
constructed, supplies the closed cone for the inverse permutation.
`positiveRootBlockSums` gives vanishing size-weighted sums of `v₀` in
each coarse block. The published `PositiveRootBlockSumsProof.transport_blockIndex` checks these
coordinates across the literal shape equality. The published
`closedConeStabilizerRigidity`, using strict decrease of the coarse
parameter, then puts the inverse permutation in the coarse block Weyl
group. Closure under inverses puts the original permutation there too.

## Actual finite series and equal positive multiplicities

`supported_positive_counts_equal` keeps the complete supported telescope.
The published all-rank theorem
`CuspidalSupport.cuspidalInductionLength` supplies the exact same-rank
standard cuspidal induction length input.
`glSupportedAmbientJacquetLengthReduction` then constructs finite
group-algebra length of the actual outer induction, finite length of
its ambient fine Jacquet module, and an actual ambient multiplicity `M`.
The fine datum's irreducibility and cuspidality are transported along the
given shape equality by `transport_irreducible_cuspidal`.

`glSupportedRelativeJacquetPositiveBound` gives an actual inner
multiplicity `m` with `0 < m` and `m ≤ M`. If the inequality is strict,
`glSupportedRegularMultiplicityBranchObstruction` supplies one
permutation outside the coarse block Weyl group, its fine-Levi conjugacy,
its real stabilizer identity, and almost-everywhere occurrence for that
same permutation and conjugacy. The preceding cone argument forces it
into the coarse block Weyl group, a contradiction. Thus `m = M`.
The helper returns the outer finite length together with the equal
positive counts. Each multiplicity predicate contains an actual finite
composition series; their existence is proved.

## Strong head

For the final theorem, real-twist invariance gives irreducibility and
admissibility of the coarse representation `πt`. Apply the published
`glRelativePositiveTotalHead` to that representation, the constructed
outer finite length, and the equal positive inner and ambient counts.
Its conclusion is the strong `HasIrreducibleHead` predicate: an actual
irreducible quotient exists, and every two surjective irreducible
quotient maps have the same kernel. No outer quotient is a premise.

The induction and Jacquet modules retain their published constructions:
upper induction uses right translation with positive half-modulus
covariance; opposite Jacquet coinvariants use the positive upper
half-modulus. The absolute value is the residue-normalized
`q^(-valuation)`.

## Provenance

This is an internal assembly of the named published proofs, implementing
the supported argument of A. J. Silberger, *The Langlands quotient theorem
for p-adic groups* (1978), Lemma 5.6, printed p.101, with the nested
support setup on p.99 and the head argument of Lemma 5.5, pp.100–101.
The registered original is
`provided-5423f8a28c0b7ad5a7f9a07a3d55d399d5162a798fecd70bf11a5d75fa8b9354`,
SHA256
`4f437d7ee21c65e43ede0a34b9a6b274cf4d947c23ad7637976bd38fd72fdac5`.
The whole original was read during this development, including the
normalization and relevant formula images.

The implemented branch theorem proves a fixed branch's occurrence for
every middle unitary parameter by geometric-piece lifting and character
twisting, and supplies the almost-everywhere assertion consumed here.
This proved algebraic route replaces the source's continuation sentence.
The remaining exclusion is the analytic tempered-exponent cone and
weighted rigidity argument described above. There is no genericity
assumption or appeal to the unrestricted wording of Lemma 5.3.

The theorem has no additional proof premise and uses no Langlands
classification or equivalent downstream result. The target pair and its
imports are unchanged. The later arbitrary-tempered reflection and
cosocle comparison are separate assertions.
