# Actual duality at the equal-rank boundary

This is an internal deduction from the published Fourier, lower-quotient,
Jacquet-section and determinant-character constructions. It proves the scalar
and supplied-measure Fourier law for the actual fixed reversed-dual section
equivalence. It also supplies two compatibility lemmas needed to apply the
first-block identity to the reversed deformed family. It does not construct
the second first-block identity or prove either final dominant-rank target.

`fourierIntegral_scale_neg_one` identifies the actual Fourier integral for
`ψ.scale (-1)` at `y` with the original integral at `-y`. This is a pointwise
identity of total integrals. `IsSelfDual.scale_neg_one` then proves that the
same additive Haar measure is self-dual for the inverse character. For a
Schwartz–Bruhat input, it transports integrability of the iterated transform
by negation, uses the published integral-under-negation formula, and applies
the original self-duality square. `negatedSelfDualHaar` retains the supplied
measure exactly and changes only its self-duality certificate.

`determinantComplexPower_inverseTranspose` uses the published determinant-norm
inverse formula and the complex power of a nonnegative real number to negate
the exponent under inverse transpose. `reversedDual_oppositeTwistBlocks`
then proves equality of the complete block-reversed inverse-transpose
opposite-twist family with the opposite twist of the complete reversed dual
family, at the same real parameter. The carriers and sizes are reversed
along with the representations. Inverse transpose negates each exponent;
reversal exchanges the two signs. This identity is at the block-family
level, and asserts no equivalence between inductions by itself.

`equalLowerGroupIntegrand_reversedDual` applies the scalar formula for
`TwoBlockDominantRectangular.reversedDualSectionEquiv` at the reflected
argument. The involutivity of `weylInverseTranspose` removes the double
reflection. The published `lowerDualTest_rotation` and
`partialSection_fourier` provide the other two factors. Their product is
the actual original group integrand times `|det g|_F`.
`equalLowerIntegrand_reversedDual` descends this identity to the actual
lower quotient and identifies the scalar as `q_F^(-ord(det g))`.

`EqualLowerFourierCoefficientLaw` is the proposition that for every actual
lower section, every Whittaker test and every supplied row Fourier pair,
the reversed determinant slice of order `-k` is integrable exactly when the
original slice of order `k` is integrable, its complex integral is
`q_F^(-k)` times the original complex integral, and its raw-norm integral
is `q_F^(-k)` times the original raw-norm integral. Both lower measures
are the transports of the same supplied standard quotient measure. The
reversed section is the image under the one fixed published section
equivalence, the test is the actual `firstDualFunction`, and the dual
block functionals are the actual `secondDualFunctional` values.

`equalLowerFourierCoefficientLaw` proves this proposition for every supplied
compatible standard quotient measure, retaining right invariance of the
canonical unipotent Haar measure. The published
`lowerDuality_measure_transport` gives exact measure preservation on each
reflected slice. The pointwise formula supplies the positive constant
`q_F^(-k)` there. The published `scalar_transport` then yields the
integrability equivalence and both total integral identities. No
scalar-section comparison, coefficient Fourier equation, or outer
integrability is assumed. The formulas for total integrals coexist with
the separately proved integrability equivalence; they do not assert that
every slice is integrable.

The canonical topology, valuation, Borel structures and residue cardinality
are used throughout the p-adic specialization. The block carriers have an
independent universe from the field. Only smoothness of the individual
blocks is required for the fixed section equivalence; no irreducibility,
nonzero functional, Whittaker-type or coefficient-image premise is needed
for this Fourier law. The supplied character is continuous and nontrivial,
as required by `UnitaryAdditiveCharacter`. A supplied self-dual additive Haar
measure and an actual row Fourier pair are retained.

This contribution does not establish ordinary Jacquet convergence,
finite numerator assembly, parameter continuation, gamma certification or
L-polynomial divisibility. Those remain separate obligations in the host
dominant-rank task.
