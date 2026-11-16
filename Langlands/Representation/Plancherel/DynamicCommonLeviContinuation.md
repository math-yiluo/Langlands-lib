# Actual common-Levi restricted continuation

This derived adapter specializes `CompactIntertwiningContinuation` and
`ContinuedIntertwiningNaturality` to the actual compact family of
`DynamicCommonLeviCompact`. The original source is Waldspurger (2003), IV.1,
printed pp.276–278 / PDF pp.42–44, registered as `waldspurger-2003-plancherel`.

The structural inputs are an arbitrary nonarchimedean local field, an affine
locally finite type connected reductive group scheme, a base cocharacter χ,
two cocharacters ψ and ψ′ whose centralizer functors equal that of χ, a compact
open K, both factorizations G(F) = P(F)K, and squared-modulus compatibility.
The inducing carrier has an independent universe uV; replacement representatives
use uW. All topologies and the literal common Levi are canonical.
The parameter algebra uses all rational characters of `parameterScheme χ`,
with exactly `normCharacters χ` and `parameterTransport χ`.

`restrictedCompactFamily` restricts the actual compact integral to Ω with a
displayed inclusion into its full convergence domain. `PairContinuation` is
exactly `RationalOperatorContinuationData` for this restricted family. Its
single denominator is chosen before the input vector and is nonzero on Ω.
`pairContinuation` uses the existing constructor from `IsRationalOperatorOn Ω`
and a nonempty open subset D of Ω; no rationality or existence is proved here.
In particular, no denominator nonzero on the whole full convergence domain is
assumed or asserted.

`continuedFamily` applies `continuedInductionIntertwiner` to the actual restricted
ambient pair integrals. Proved radical unimodularity, closedness, projection
continuity and norm-character continuity discharge its structural inputs. The
centralizer scheme is connected reductive and its valuation-image projection
is continuous by existing results. Polynomiality of the varying compact actions
and propagation of equivariance are supplied by the generic machinery.
The result is an actual ambient intertwiner on the chosen denominator's nonzero
locus; it makes no claim about values at poles or a maximal continuation domain.

`continuedFamily_compact` identifies compact conjugation with the rational
continued operator by the generic compact equivalence cancellation.
`continuedFamily_agrees` recovers the original actual pair integral on Ω.
`continuedFamily_spec` consequently gives its original `HasIntegral` there:
all ambient group arguments and smooth-dual functionals are retained and the
value is represented in the original inducing carrier with the unchanged
`pairQuotientMeasure K hK ψ ψ′`. `continuedFamily_unique` invokes generic
uniqueness to compare arbitrary numerator/denominator choices on their common
regular locus, using the explicitly supplied nonempty open D inside Ω.

`continuedFamily_natural` permits independently chosen starting regions Ω and Λ
and independently chosen continuation data for equivariantly equivalent inducing
representatives. It requires one common nonempty ambient open set D contained
in both regions. The original square follows from the actual `pairFamily_natural`
proved in the compact module; generic rational uniqueness propagates it to every
common regular value. The vertical ambient maps are the inducing equivalence
twisted by the same transported character, followed by `inducedMap`. Membership
proofs differ only by proof irrelevance. No assumed square or preservation of
rationality is used. The compact module already proves the inverse-cocharacter
specialization to the published conditional opposite compact family, with the
existing conditional squared-modulus witness.

This unit proves elementary continuation adapters conditional on actual data.
Analytic existence, regularity at all unitary parameters, invertibility and
normalized tensor comparisons remain separate obligations.
