# Full rank-one witness cosets

Worker 1813 implements derived helpers, following Worker 1786's proposed character-separation and epsilon-cancellation subproblem. Workers 649,
655 and 394 are credited for the shared published helper implementations.
This module provides derived helpers for the unchanged rank-one stability
target. These helpers retain every prime, arbitrary p-adic carrier universe,
and supplied topological data. They prove character separation and uniqueness
relative to one witness. They do not prove that a twist witness exists. The primary construction
`separatingQuasicharacter` returns an actual continuous quasicharacter whose
conductor bound and detecting value are certified in its subtype. It takes
only nonmembership in the prescribed principal-unit subgroup and chooses
from the existence result proved by quotient separation.

## Bounded-conductor separation

The actual subgroup `T.principalUnits k` is open. The valuation-one condition
is the inverse image of an open valuation sphere, transported through the
actual ordered value-group isomorphism. The congruence condition is the inverse
image of the open integer ring by `v ↦ (v - 1) / uniformizer^k`. The published
filtration membership criterion identifies their intersection with the
principal-unit subgroup, including level zero.

The quotient by this open subgroup is a discrete abelian group. Mathlib's
character-module separation theorem detects each nonidentity element using
the rational circle. The injective embedding of the rational circle into
the real circle, followed by `AddCircle.toCircle` and `Circle.toUnits`, gives
a character into the complex units. Its continuity follows from the discrete
domain. Pullback to the field units gives an actual continuous quasicharacter
trivial on `T.principalUnits k`, hence of conductor at most `k`.
Consequently an element belongs to this principal-unit subgroup if and only
if every quasicharacter of conductor at most `k` takes value one there.
The proof covers all natural `k`, including zero.

The discrete character construction and openness theorem are reused from
[`Langlands.HarmonicAnalysis.CharacterSeparation`](../HarmonicAnalysis/CharacterSeparation.md),
which contains the unchanged helpers extracted from
`Langlands.HarmonicAnalysis.UnboundedConductorProof`. It credits Workers 649,
655 and 394 for that implementation. In particular, the shared
`Langlands.HarmonicAnalysis.CharacterSeparation.principalUnits_isOpen` replaces
the local copy. This module uses that established elementary route on an
arbitrary supplied topology, with the quotient taken at the prescribed level.

## Exact witness coset

`epsilon_ne_zero` specializes the published `epsilonAt_ne_zero` theorem to
the actual constructed conductors. In particular, it makes no nonvanishing
assumption and retains the supplied Haar measure.

For a fixed witness `gamma`, a second witness `gamma'` has the same epsilon
identity for every allowed twisting character. Choose any normalized regular
Haar measure, evaluate at spectral parameter zero, and cancel the nonzero
epsilon value. This gives `eta(gamma') = eta(gamma)` for every allowed `eta`.
The numerical range `2*a(eta) <= a(chi)` is exactly
`a(eta) <= a(chi)/2`, with natural-number division. Applying character separation
to `gamma' * gamma^(-1)` therefore proves membership in
`T.principalUnits (a(chi)/2)`.

Conversely, membership in this subgroup forces the two character evaluations
to agree throughout that same range. Substitution in the existing witness's
identity gives the identity for `gamma'`, for every regular additive Haar
measure and every complex spectral parameter. No valuation restriction on
`gamma'` is required. Both directions include the even-conductor endpoint.

This is an internal proof of the uniqueness consequence of the existing
target's witness predicate, using the published actual conductor and epsilon
constructions. The original-source convention for that target is documented
in `RankOneStabilityStatement.md`. The lemma takes one witness only to describe
its complete coset; the full target still requires an unconditional
construction of such a witness.
