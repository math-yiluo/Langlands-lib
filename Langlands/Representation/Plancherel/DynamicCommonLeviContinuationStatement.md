# Actual common-Levi existence target

`Langlands.Plancherel.DynamicCommonLeviContinuation.ConditionalDynamicCommonLeviContinuationStatement`
is a closed proposition, with independent field and inducing-carrier universes.
It states the remaining common-Levi existence consequence of Waldspurger (2003),
IV.1.1, printed p.278 / PDF p.44, with the integral and compact-picture conventions
of IV.1 pp.276–278. The registered source is `waldspurger-2003-plancherel`.
This is a derived interface target, not a new complete formulation of IV.1.1's
full-root cone theorem, which is already stated as
`ConditionalParabolicIntertwiningStatement`.

The exact structural inputs are an arbitrary nonarchimedean local field F;
an affine locally finite type group scheme G with `IsConnectedReductive G`;
three cocharacters χ, ψ, ψ′; equalities of the latter two centralizer subgroup
functors with χ's centralizer; a common compact open K and its compactness;
the two displayed factorizations G(F) = P(ψ)(F)K and G(F) = P(ψ′)(F)K;
and an admissible finite-length canonical `SmoothRep` on the literal Levi χ.
There are no additional root-reflection, split-center, realization, analytic,
normalization or invertibility hypotheses in this target. Canonical point
topologies, proved closedness, radical unimodularity, projection continuity
and norm-character continuity are reused by the construction.
No restriction on characteristic, splitness, quasisplitness or rank is made.

`CommonLeviContinuationExists` spells out its conclusion for fixed structural
data: squared-modulus compatibility, a nonempty open character set Ω, a displayed
inclusion Ω into the actual `pairFullDomainRegion`, rationality of the actual
restricted compact integral on Ω, and nonempty `PairContinuation` data for that
same family. The quotient measure is exactly `pairQuotientMeasure K hK ψ ψ′`.
The parameters use all rational characters of `parameterScheme χ`, exactly
`normCharacters χ`, and `parameterTransport χ` to the literal common Levi.

The quantifier order in `IsRationalOperatorOn` selects one regular denominator
before the input vector and requires it to be nonzero throughout Ω. Each fixed
input vector then has a finite polynomial expression after multiplication by
that same denominator. The continuation-data conclusion is an elementary
consequence of this rationality and the nonempty openness of Ω: apply the
published `pairContinuation` constructor with D = Ω and inclusion `Subset.rfl`.
Its `continuedFamily` is the constructed actual ambient intertwiner; the previous
module proves compact conjugacy, recovery, choice independence and naturality.
The explicit nonempty-data clause exposes this usable output in the target.

There is no assumed convergence, rationality or existence clause in the closed
target's premises. Squared-modulus compatibility is also a conclusion. Neither
this target nor the construction asserts a denominator nonzero on the entire
full convergence domain. IV.1.1 supplies rationality on a saturated cone; obtaining
an appropriate restricted open start from that result is the presentation
comparison obligation addressed separately. No value at a pole, maximal regular
domain, unitary regularity, invertibility, tensor comparison, composition or scalar
identity is asserted.
