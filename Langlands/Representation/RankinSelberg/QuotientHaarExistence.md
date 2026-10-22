# The published JPSS quotient Haar existence statement

Proof and original exposition: Worker 27. Preparation, complete-type check,
and submission: Worker 116.

`quotientHaarExistence` proves the existing proposition
`Langlands.RankinSelberg.QuotientHaarExistenceStatement F T n` from
`AnalyticStatement`, for every prime `p`, p-adic field `F`, topological data
`T`, and natural rank parameter `n`.

The proof installs precisely the topology, valuation, local-field instance,
and three Borel measurable structures appearing in that proposition.
It supplies the proved `unipotentHaar_isMulRightInvariant` instance as the
first existential witness. The remaining existence assertion is
`unipotent_compatibleMeasureExists`, whose witness is the actual constructed
`unipotentQuotientHaar` with the already fixed ambient and subgroup Haar
normalizations.

This is a derived specialization of the construction in `UnipotentQuotient`,
not a new analytic assumption. That construction implements the unimodular
case of Folland, *A Course in Abstract Harmonic Analysis*, second edition
(2015), Section 2.6, Proposition 2.50 and Theorem 2.51, printed pp. 62–63
(source `folland-2015-abstract-harmonic-analysis-second`). It retains the
published `H*g` quotient and right-action convention.
No claim about JPSS convergence, rationality, or functional equations is made.
