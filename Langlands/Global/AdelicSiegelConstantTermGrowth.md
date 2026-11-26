# Siegel chamber growth under constant-term averaging

On a fixed weak simple-root chamber times a compact set of right factors, a function with
`HasSiegelChamberGrowth` is bounded by the square root of the Siegel modulus times a power
of one plus the logarithm of the adelic matrix height at the torus point.

`hasSiegelChamberGrowth_constantTerm` shows that constant-term averaging preserves this
bound for functions invariant under the rational group. Compact representatives of the
radical quotient map into the minimal radical. Conjugation by the inverse torus point
puts these representatives in one compact set as the torus point ranges over the chamber.
Their effect on the argument is an enlargement of the compact right factors. The measure
on the unipotent quotient is a probability, so averaging preserves the resulting bound.

`hasSiegelChamberGrowth_of_logSquareIntegrable` obtains the chamber estimate for the
original form from `LogSquareIntegrableSiegelDerivativeBoundsStatement` by taking the
empty derivative word. The submultiplicative matrix height is bounded on the compact
right factors, so one plus the logarithm of the height of the torus coordinate controls
the logarithmic height of the full point. `AdelicSiegelConstantTermGrowthStatement`
combines this specialization and the averaging result.

Delorme uses the sharp logarithmic Siegel estimate to bound constant terms in
*On the Spectral Theorem of Langlands* (2023), Proposition 3.6, equation (3.4), pp. 13–14.
The proof here uses compactness of the inverse unipotent conjugates as in §2, (2.4),
and direct probability averaging.
