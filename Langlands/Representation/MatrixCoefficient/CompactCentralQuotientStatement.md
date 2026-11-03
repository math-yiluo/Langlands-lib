# Square integrability on a compact full central quotient

`Langlands.CompactCentralQuotientSquareIntegrabilityStatement` states that an
admissible algebraic complex representation of a topological group, with a
genuine unitary central character, is square integrable modulo its full group
center whenever that quotient is compact.

The group and representation carrier have independent universes. The carrier
has no topology. The quotient uses its existing quotient topology, an arbitrary
Borel measurable space and any supplied Haar measure. The conclusion is the
published `IsSquareIntegrableModCenter`: admissibility together with a genuine
unitary central character whose descended coefficient norms are in `MemLp` at
exponent two for every smooth-dual functional and every vector.

This is an internal analytic reduction. The intended proof uses the published
`UnitaryCentralCharacter.continuous_coefficientNorm`, smoothness of every vector
from admissibility, compactness of the coefficient's topological support in a
compact space, and Mathlib's
`Continuous.memLp_of_hasCompactSupport`. Haar measures are finite on compact
sets, so no normalization of the supplied measure is needed.

This statement does not prove compactness of any particular group's central
quotient. In particular, applying it to the empty-root case of the general
rational strict Jacquet criterion still requires a proof of that geometric
compactness. No classification, Jacquet asymptotics or spectral decomposition
is part of this reduction.
