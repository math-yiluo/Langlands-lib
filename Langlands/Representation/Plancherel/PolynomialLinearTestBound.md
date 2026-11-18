# Bounds for algebraic tests of polynomial numerators

The primary construction is
`Langlands.Plancherel.UnramifiedOperatorFamily.linearTestOnPolynomialSpan`.
It restricts an arbitrary algebraic complex linear functional to the intrinsic
finite-dimensional value span of a polynomial vector family, where the
functional is continuous. The ambient carrier may be infinite dimensional,
and the functional need not be continuous on it.

`polynomialValueSpan` is the span of the family's actual values. A finite
expansion witnessing the existing `IsPolynomialOn` puts this span inside the
span of finitely many fixed vectors, proving finite dimensionality. The span
construction and this argument require no carrier topology.

For a normed complex carrier, restriction of the functional to this span
gives a continuous linear map. Its operator norm bounds the functional on
every value of the family. The denominator-bound consequence composes that
bound with a supplied cleared vector estimate
`norm(f(z)) ≤ A * norm(b(z))` on a specified parameter subset, with `A ≥ 0`.
The resulting scalar estimate retains the same regular denominator; only the
constant may depend on the functional.

This is an internal finite-dimensional linear-algebra step in the route from
unitary norm identities to scalar pole cancellation, as used in Waldspurger
(2003), Corollary V.2.3 and Lemma V.3.1 (printed pp.294–295 / PDF pp.60–61;
registered source `waldspurger-2003-plancherel`). It does not supply any
standard-family norm identity, pole-support theorem or regular extension.
