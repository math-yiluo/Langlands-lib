# Two outer parity prefixes for the positive-inner filtration

This module gives a concrete two-prefix reduction for the
positive-inner linked case. It applies to positive original absolute weights
`L,M`, a linked index `k` and positive signed inner weight `H`.
The kernel-image containment is an explicit premise; it is not
proved here (`RealInducedPairPositiveFiltration` proves it, by
`ker_le_totalPrefix` and `absorption_iff_ker_le`).

For any compatible endpoint parity choices `sd,se`, `parityPrefix` is the
actual inner binomial followed by the actual original two-block quotient.
`prefix_realization` generalizes the existing realization to these arbitrary
parities. The two generic middle crossings are onto. The outer rank-one
decomposition therefore realizes this prefix as the sum of the ranges of
an exact exchanged-pair map `qW` and an outer-source map `qR` intertwining
modulo `range qW`. Every map used is an existing actual Frobenius or quotient
map; no range equality or intertwiner is assumed.

`oppositePrefix` uses the simultaneous flips of both endpoint parities from
the positive crossed construction. Its outer source is the proved
`oppositeOuter`. Define

`totalPrefix = range(original prefix) + range(oppositePrefix)`.

Each of the two outer sources preserves exponent support and has squared
weight `P^2`, where `P=L+M+H`. Both are therefore allowed strictly heavier
sources. The exchanged pair is also an allowed source.

Let `T` be the existing actual `middleSection` from the positive mixed source,
and `U` its existing exact onto crossed quotient. `Absorption` is precisely

`T(ker U) ≤ totalPrefix`.

The proved kernel decomposition
`ker(positiveCrossedQuotient) = range(original prefix) + T(ker U)`
shows that this premise is equivalent to containment of the entire positive
crossed quotient kernel in `totalPrefix`
(`absorption_iff_ker_le`). No reverse containment of `totalPrefix` in that
kernel is needed or asserted.

Assume `Absorption`. The map `T` already intertwines modulo the original
prefix, hence modulo `totalPrefix`. The actual quotient-descent theorem
replaces its source by the heavier crossed pair, producing a map `qC`
intertwining modulo `totalPrefix`. Its range together with `totalPrefix`
spans the entire original two-block module.

The helper `five_piece` assembles the maps in the order
`qW0,qR0,qW1,qR1,qC`. The repeated exchanged-pair source is permitted:
both such maps intertwine exactly; each outer map intertwines modulo its
own earlier exchanged range; the crossed map intertwines modulo all four
earlier ranges. The actual spanning identity proves this is a filtration.
The allowed-source checks then give `filtration`.

`RealInducedPairPositiveTwoPrefixStatement` packages exactly the implication
from this explicit `Absorption` premise to the actual positive-inner adjacent
filtration. `realInducedPairPositiveTwoPrefix` proves it.

The provenance is the existing actual positive crossed kernel, rank-one
decompositions, generic middle surjectivity, outer-parity arithmetic, and
surjective quotient descent. This module leaves all earlier chosen maps
unchanged. It proves neither `Absorption` nor the unrestricted
`RealInducedInducedFiltrationStatement`. No finite computational experiment
is used as mathematical evidence.
