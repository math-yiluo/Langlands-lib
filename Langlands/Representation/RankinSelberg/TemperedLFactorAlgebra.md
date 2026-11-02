# Algebraic reductions for tempered pair L-factors

Worker 40 authored these internal auxiliary reductions for
`Langlands.RankinSelberg.TemperedLFactorStatement`. They are in namespace
`Langlands.RankinSelberg.TemperedLFactorAlgebra`. Analytic multiplicativity,
existence and pole bounds remain explicit premises where used; these lemmas
do not by themselves prove the closed tempered statement.

The defined type `NormalizedPolynomialQuotient P B` stores a complex polynomial
`polynomial`, its normalization `polynomial.coeff 0 = 1`, and the identity
`B = polynomial * P`. Its two constructors choose a residual from a Laurent
divisibility relation or from the two-family divisibility reduction below.
They retain the hypotheses of those reductions. The structure packages the
residual used in the original and dual polynomial factorizations; its existence
alone does not identify the residual with one.

Normalization reuses `IsPadicPairLPolynomial.coeff_zero` and
`IsPadicSymmetricLPolynomial.coeff_zero` from
`PadicPairLPolynomialNormalization`. The pair relation supplies a compatible
quotient measure; `IsPairLPolynomial.coeff_zero` applies at that measure. The
symmetric relation is reduced to its chosen rank-order branch.

The pole-bound reduction assumes a Laurent divisibility identity
`X^e B = R P`, normalization `P.coeff 0 = 1`, and zero-freeness of `B` in the
open unit disk. At zero, normalization proves nonvanishing. At a nonzero point,
evaluating the identity shows that a zero of `P` would force a zero of `X^e B`,
contradicting the hypotheses. The finite-product lemma proves that zero-freeness
of each block polynomial gives zero-freeness of their double product.

The quotient reduction removes the Laurent power of `X` by induction. In the
successor case, evaluation at zero forces the constant coefficient of the
quotient to vanish, so `X` divides it. Canceling `X` reduces the exponent by
one. Taking constant coefficients afterward shows that the resulting polynomial
quotient has constant coefficient one whenever both `B` and `P` do.

The double-product reduction applies that quotient extraction first to the
outer family and then separately to every row of block polynomials. Multiplying
the row identities gives the residual quotient as the product of the row
quotients times the outer quotient. Evaluation at zero proves that every
quotient and their product are normalized. A separate evaluation argument
shows that a quotient of a zero-free product has no zero in the same disk.

The rational cancellation lemma starts from the explicit equality of the
original/product polynomial ratios, with their duals under reciprocal
substitution and an explicit Laurent monomial. Nonzero polynomials stay nonzero
under the rational-function embedding and reciprocal substitution, so the proof
cross-multiplies, substitutes the residual factorizations, and cancels the
original and reflected dual factors. The resulting identity relates the two
residuals. The lemma does not derive the input ratio from gamma multiplicativity.

The reflection reduction imports the published `reflectionRigidity` proof and
specializes both root-exclusion radii to one. Given normalized residuals
`B = D * P` and `Bdual = E * Pdual`, the two product pole bounds imply the
required pole bounds for `D` and `E`. The supplied reflected rational identity
then gives `D = E = 1`, hence both polynomial product equalities and the original
pole bound. A separate lemma verifies the strict norm bound for the canonical
residue reflection using that the residue cardinality is greater than one.
The reflected identity and both product pole bounds remain explicit premises.

The certified square-integrable reduction takes
`SquareIntegrablePoleFreeStatement` as an explicit hypothesis. That hypothesis
supplies a certified polynomial with the pole bound; published uniqueness
identifies it with any other certified polynomial of the same pair. This
conditional reduction does not prove the analytic square-integrable result.

These are internal elementary consequences of the published polynomial
definitions and the divisibility/pole-free interfaces. The intended final
application is JPSS, *Rankin–Selberg Convolutions* (1983), Proposition 8.4,
printed pages 451–452. The final application must supply certified factor existence, original and
dual divisibility, block pole bounds and the reflected identity relating the
residual quotients. The reflected-root comparison is imported from
`Langlands.Representation.RankinSelberg.ReflectionRigidityProof`;
normalization is extracted from the intrinsic Library certificate rather than
assumed for each application. This is a derived algebraic contribution; it
asserts no new analytic theorem from the cited literature.
