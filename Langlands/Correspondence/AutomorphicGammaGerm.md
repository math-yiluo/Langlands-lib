# Spectral germs and orders of certified automorphic gamma factors

This internal interface converts the existing rational gamma expression into
the meromorphic function used by pole counting and transfers the unitary
arithmetic order bound through a supplied pair gamma match.

## The spectral expression

For an integer `q > 1`, `polynomialGammaExpression q c m P Pd` is the function

`s ↦ epsilonMonomial q c m s * (Pd.eval (spectralPoint q (1 - s)))⁻¹ /
  (P.eval (spectralPoint q s))⁻¹`.

Thus it uses the existing epsilon monomial and the original and reflected
reciprocal L-polynomials. Division and inversion are complex field operations;
the values at a singular center do not specify the meromorphic germ.

`analyticAt_polynomial_spectralPoint` proves analyticity by composing a
polynomial with the exponential expression for the published spectral point.
`polynomial_spectralPoint_eventually_ne_zero` shows that a nonzero polynomial
remains nonzero on a sufficiently small punctured neighborhood of any complex
point. It packages the entire spectral denominator as `ReciprocalEntire`.
Nontriviality follows from the existing finiteness of real spectral zeros,
and `denominator_eventually_ne_zero` supplies punctured nonvanishing.
`polynomial_reflected_spectralPoint_eventually_ne_zero` applies the same
argument after reflection `s ↦ 1 - s`.

`meromorphicAt_polynomialGammaExpression` proves that the displayed expression
is meromorphic everywhere using analyticity of the epsilon monomial and both
polynomial evaluations, followed by meromorphic inversion, multiplication and
division. This assertion itself needs no nonzero-polynomial hypothesis.

`rationalSpectralValue_eventuallyEq_polynomialGammaExpression` assumes `Pd ≠ 0`
and that the rational reflection scale is `q⁻¹`. At each complex point it proves
equality on a punctured neighborhood between rational spectral evaluation and
the displayed expression. The proof uses reflected punctured nonvanishing and
the existing `eval_rationalGammaExpression` formula. It does not assert equality
of numerical values at a singular center.

## Actual automorphic certificates

`IsAutomorphicPairGammaFactor.eq_rationalGammaExpression` accepts a gamma
certificate together with any supplied genuine smooth-dual classes, L-polynomial
certificates `P`, `Pd`, and epsilon certificate `e`, all for the same character
and measure. The proved class contragredient characterization makes the dual
classes unique. The existing uniqueness results for certified class L-polynomials
and epsilon factors then identify these supplied witnesses with the gamma
certificate's existential witnesses. The conclusion is an equality of rational
functions with the supplied expression.

`IsAutomorphicPairGammaFactor.rationalSpectralValue_eventuallyEq` applies the
general germ theorem to that rational identity and the actual residue
cardinality and reflection. The certified dual L-polynomial is nonzero by its
normalization. These results retain independent field and automorphic carrier
universes.

## Order transfer

`IsPairGammaMatch.polynomialGammaExpression_order_nonpos` takes an actual
`IsPairGammaMatch` for classes of two local Weil–Deligne representations with
unitary underlying Weil actions. For any supplied self-dual measure and the
same dual, L and epsilon certificates as above, it proves that the displayed
automorphic expression has nonpositive meromorphic order at every `s` with
`s.re ≠ 0`. The pair match gives a common rational gamma factor. The germ
theorem and `meromorphicOrderAt_congr` identify its automorphic order with
its rational spectral order. The published
`IsArithmeticPairGammaFactor.order_nonpos_of_isUnitary` gives the bound.
The field, parameter carrier and local-constant assignment universes remain
independent, while automorphic classes use the field carrier universe required
by the published `IsPairGammaMatch` interface.

`localSelfPair_polynomialGammaExpression_order_nonpos` specializes this result
to restriction of a unitary relative Weil representation `S` and its actual
dual along a supplied local Weil map. Restriction and finite-representation
duality preserve unitarity. The companion
`localSelfPair_polynomialGammaExpression_real_positive_order_only_zero`
proves that positive order at a real point forces that point to be zero,
by contradiction with the nonpositive bound. The original number fields,
arithmetic representation carrier and local-constant assignment universes
remain independent.

## Provenance and scope

This is a derived internal construction using the published Library meanings
of rational gamma expressions, class factor and genuine smooth-dual relations,
spectral root finiteness, `ReciprocalEntire`, and the proved unitary arithmetic
order bound. It makes no new original-source assertion. Its role in the
associated-pair proof is to connect those existing interfaces without losing
the punctured germ at a zero or pole.

The pair gamma match, self-dual measure and automorphic factor certificates
are explicit inputs. This module does not prove their existence, construct a
global contragredient cuspidal realization, prove classification or block
factor identities, or prove `AssociatedSupercuspidalInductionStatement`.
