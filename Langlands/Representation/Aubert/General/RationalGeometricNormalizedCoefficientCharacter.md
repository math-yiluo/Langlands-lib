# The original normalized coefficient and both epsilon corrections

This internal prerequisite compares the original compact coefficient character
with the two original epsilon corrections on the entire literal common Levi.
The whole common-Levi balance and the exact geometric K0 expansion remain open.

Let `Lt = (M_I intersect n M_J n⁻¹).subgroupOf M_I`, and let `c` be its
published inclusion in the literal target intersection
`K = (M_I intersect n P_J n⁻¹).subgroupOf M_I`. The original coefficient map
`p` is the actual target Levi projection followed by inverse conjugation.
`geometricCoefficientLeviMap_commonLevi` proves `p.comp c = e`, where `e`
is the original inverse-conjugation equivalence of the common Levis. The proof
uses the supplied target decomposition's identity on its Levi; both nested
subgroup copies are retained.

`geometricInducingHalfCharacter_commonLevi` consequently identifies the original
inducing half, after restriction through `p` and `c`, with the canonical positive
half of the forward-conjugate original source-radical modulus. It uses the
published inverse-conjugate/forward-conjugate modulus equality and then unfolds
the actual half-character at each common-Levi element.

`geometricNormalizedCompactEndpointRatioCharacter` names the remaining
positive target-endpoint half times the inverse source-endpoint half on `Lt`.
This definition uses the literal original intersection moduli.

Write `u,v,a,b,c₀` for the original target radical, forward source radical,
source endpoint, target endpoint and common radical Haar characters on `Lt`.
`geometricNormalizedCompactCharacter_commonLevi` proves that the actual
normalized compact character restricts to `sqrt(u) sqrt(v) / (a c₀)`. The proof
uses the published factorization of the full correction modulus into `a c₀`,
the original radical restriction and the preceding inducing-half identity.
It transports the resulting positive-unit equalities through the original
complex-unit homomorphism.

`geometricNormalizedCompactCharacter_commonLevi_eq_epsilonProduct` rewrites
this as `epsilonOne epsilonTwo sqrt(b) / sqrt(a)`. Both epsilons are the
published original corrections. The proof substitutes their whole-common-Levi
factorizations, applies the canonical positive-square-root square identity to
`a` and `c₀`, and cancels the remaining factors in the commutative complex-unit
group. In particular, this equality retains both epsilon corrections and
assumes no distinct-radical balance. Identification of the final half-character
ratio with both original normalized geometric-term endpoints, and extension
through the full target intersection, are separate obligations.

The first two lemmas use only their displayed semidirect, closedness and ambient
topological hypotheses. The last two additionally retain
`StandardCocharacterStatement`, connected reductivity, a maximal split torus,
a generic cocharacter, point-normalizer comparison, second countability, the
stated closed parabolics and Levis, and continuity of the indicated original
Levi projections. All results quantify over the original field universe, root
subsets and actual torus-normalizer point. No minimal representative or rank
restriction is imposed.

These are internal deductions from the actual compact comparison, original
correction characters, their published factorizations and character algebra.
They add no geometric expansion, orbit comparison, adjointness, cuspidal
support, character independence or classification premise. The broader
imported-module closure is inherited from the named modules. Full character
balance, compact/full induction, proper graded comparison, ordered filtration
and the unapplied exact-K0 expansion remain open.
