# Conditional gamma constructor and its rational functional equation

Worker 31, with Worker 11 contributing the finite-exception spectral-point
proof method. The module `Langlands.RankinSelberg` constructs a unit rational
function from the published pair epsilon and L-factor constructors:

\[
\gamma(X)=\epsilon(X)\frac{L^\vee(q^{-1}/X)}{L(X)}
          =cX^m\frac{P(X)}{P^\vee(q^{-1}/X)}.
\]

It proves the corresponding unnormalized functional equation whenever a
normalized equation uses these same intrinsic polynomials and epsilon data.
The conclusion excludes only zeros of the reduced denominators of the two
continuations and gamma. In particular, a zero of the displayed polynomial
`Pdual` that cancels in the rational expression is allowed.

## Source and scope

Jacquet--Piatetski-Shapiro--Shalika, *Rankin--Selberg convolutions* (1983),
Theorem 2.7(ii)--(iii), printed page 391, gives `L = 1/P`, `P(0) = 1`, and
the normalized equations with `epsilon(s) = c q^(-ms)`. Rearranging those
equations gives the ratio above. The central-character scalar remains outside
gamma: in the source it is `omega_sigma(-1)^(rank(pi)-1)`.
The dual is the inverse-transpose pullback of Section 2.1, formula (4),
printed page 386, using the character `psi.scale (-1)` as in `PairLFactor`.
It has not been identified here with the smooth contragredient. The Fourier
normalization is the shared plus-sign transform and self-dual additive Haar
measure from the notation section, printed page 378.

The unit constructor, regular-evaluation helpers, and rational-identity
argument are derived formal consequences of these formulas. The proof by
agreement at infinitely many spectral points is an algebraic implementation;
it does not claim to formalize the source's analytic existence proof.

This module imports `PairLFactor`, `PairEpsilonFactor`, and the helper
`RationalEvaluation`. It reuses the shared `RationalReflection.subst` and
`WeilDeligne.reflectionScale`. Epsilon constructors and uniqueness are
imported, not redefined. The new evaluation lemma connects their rational
and complex values.

Existence of epsilon and of both intrinsic L-polynomials is required as
input. Their separate existence proofs do not identify the intrinsic
L-polynomials with the generators attached to every individual Whittaker
functional in `EpsilonEquation`. Thus this module does not establish the
universal relation `IsPairGammaFactor` or analytic existence. That comparison,
rank exchange, additive-character change, twists, and nongeneric Langlands
data remain separate obligations.

## Parameters and normalization

The field `F : Type uF` has field, valuative relation, topology,
nonarchimedean-local-field and measurable structures. Complex representations
`pi` and `sigma`, on carriers of independent universes `uV` and `uW`, act
on `GL_(r+1)(F)` and `GL_(n+1)(F)`. The latter group and its upper unipotent
subgroup have Borel measurable structures, and the left unipotent quotient
has a measurable structure. The constructors also require `BorelSpace F`,
`T2Space F`, and `TotallyDisconnectedSpace F` for `IsSelfDual psi nu`.

`q : Nat` and `abv : AbsoluteValue F Real` are explicit parameters. A p-adic
application supplies the residue cardinality and normalized absolute value;
this module does not assert that an arbitrary `q` or `abv` has that meaning.
The gamma constructor requires `1 < q`, `IsSelfDual psi nu`, right invariance
of the unipotent Haar measure, and quotient-measure compatibility
`IsCompatible (upperUnipotent ...) (generalLinearHaar ...) (unipotentHaar ...) mu`.
Both L-polynomial existence hypotheses use the same `mu` and `nu`. The
compatibility and self-duality proofs are explicit inputs even though the
algebraic expression does not compute from them.

Rank one is `n = 0`. The imported relations distinguish `n < r`, `n = r`,
and the false branch `r < n`. The constructor therefore covers the first
two cases, conditional on its existence inputs; it does not supply factors
in the reversed-rank branch.

## Evaluation and reflection

`spectralPoint_one_sub` proves `spectralPoint q (1-s) = q^(-1) /
spectralPoint q s` by comparison with the arithmetic spectral parameter and
its reflection formula. `eval_rationalEpsilonMonomial` proves that the
rational unit `c X^m` evaluates to `c z^m` for `z != 0`, using regular
multiplication and integer powers. `regular_rationalEpsilonMonomial` obtains
reduced-denominator nonvanishing from this nonzero value.
`eval_pairEpsilonFactor` specializes to the nonzero spectral point and
identifies the result with `pairEpsilonValue`. This lemma does not require
the right-invariance instance needed for the gamma constructor.

`rationalGammaExpression delta c m P Pdual` defines the displayed expression
`c X^m P(X) / Pdual(delta/X)` for arbitrary polynomials. This auxiliary
expression asserts no factor relation or nonvanishing. The lemmas
`regular_rationalGammaExpression` and `eval_rationalGammaExpression` apply
when `z != 0` and `Pdual(delta/z) != 0`; they use the helper module's
regularity and evaluation of polynomial substitution and division.

## From the normalized equation to a rational identity

`NormalizedFunctionalEquation.gamma_value` rearranges the normalized equation
at `s`, assuming both continuation denominators and
`Pdual(spectralPoint q (1-s))` are nonzero. Its proof multiplies by the last
nonzero scalar, applies the equation, and clears the denominator.

`NormalizedFunctionalEquation.rational_gamma_identity` assumes `q > 1`,
`delta = q^(-1)` as complex scalars, and `Pdual != 0` as a polynomial.
Writing `G = rationalGammaExpression delta c m P Pdual`, it proves

\[
\operatorname{subst}_{\delta}(R^\vee)=\zeta^e(GR).
\]

The proof removes the finite sets of real parameters where the original
continuation denominator, reflected dual denominator, or reflected `Pdual`
vanishes. The published injectivity of the real spectral parametrization
makes the image of the complement infinite. At each point in this image,
regularity and evaluation of the shared substitution, products, and gamma
expression turn `gamma_value` into agreement of the two rational functions.
The published `rationalFunction_eq_of_infinite_eval_eq` then proves equality.

`NormalizedFunctionalEquation.gamma_value_of_regular` evaluates this identity
at any complex `s` where `R`, `Rdual`, and `G` have nonzero reduced denominators
at their respective spectral points. It requires `Pdual != 0` as a polynomial
but no longer requires its value there to be nonzero. This distinction is
what permits canceled polynomial zeros. Neither lemma interprets a rational
function at a pole as an analytic value.

## Constructor and equation for a pair

`pairGammaFactor hq hnu hmu hepsilon hL hdual` multiplies the epsilon unit by
the reflected dual L-unit and divides by the original L-unit. Substitution
is mapped to units through its monoid homomorphism. All unit fields are
therefore proved by the imported units and algebra homomorphism.
`coe_pairGammaFactor` gives the exact rational-function ratio.

`pairGammaFactor_eq` identifies this ratio with
`c X^m P(X) / Pdual(q^(-1)/X)` for any witnesses satisfying
`IsPairEpsilonFactor`, `IsPairLPolynomial`, and `IsDualPairLPolynomial`.
It uses the published uniqueness and witness-identification lemmas, the
shared substitution on polynomials, and field algebra.
`pairGammaFactor_eq_expression` records the same equality using the new
auxiliary expression. Hence these descriptions do not depend on the chosen
witnesses.

`pairGammaFactor_functional_equation` additionally takes an actual
`NormalizedFunctionalEquation q P Pdual zeta c d m R Rdual` for those same
witnesses. It rewrites gamma to the expression above, obtains polynomial
nonvanishing from `IsDualPairLPolynomial.ne_zero`, and applies
`gamma_value_of_regular`. Its conclusion is

\[
R^\vee(q^{-(1-s)})=\zeta^d\gamma(q^{-s})R(q^{-s})
\]

on the full common reduced-denominator domain. The scalar `zeta` and exponent
`d` are arbitrary parameters of this conditional algebraic theorem; identifying
them with the source's central character and rank is the responsibility of
the supplied normalized equation.
