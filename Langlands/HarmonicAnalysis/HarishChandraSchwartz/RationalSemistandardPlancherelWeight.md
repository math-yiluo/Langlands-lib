# Actual Plancherel density on every intrinsic semistandard orbit

Worker 268. Namespace
`Langlands.HarishChandraSchwartz.RationalSemistandard.SourceDensity`.
This derived adapter supports Task 7258's source wave packets. It uses the
actual dynamic scalar package and actual intrinsic semistandard coefficient
fibers, rather than introducing a free density.

The original source is J.-L. Waldspurger (2003), *La formule de Plancherel
pour les groupes p-adiques*, registered as `waldspurger-2003-plancherel`,
SHA256 `4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
V.2 and Lemma V.2.1, printed page 292 (PDF page 58), define the density
on unitary discrete-series orbits. VI.3, printed page 302 (PDF page 68),
uses it in the actual wave-packet integral. This file generalizes the
standard-specific assembly in `StandardLeviPlancherelWeight`, reusing its
published generic smooth-pullback and orbit-descent proofs. It supplies no
new analytic continuation or scalar-regularity proof.

The field has arbitrary characteristic and independent universe `u`;
representation carriers have universe `uV`. The connected reductive ambient
group scheme is affine and locally of finite type, with the canonical point
topology. The intrinsic semistandard index `t` and its actual `LeviModel`
are the published ones. No ambient splitness, quasi-splitness or
representation-carrier topology is added. Rank zero is included.
An explicit `CocharacterPresentation hG t` identifies its entire actual
all-test triple with a cocharacter triple. The preceding adapter constructs
such a presentation conditionally from the separately owned dynamic-
coverage target. This file assumes only the actual presentation witness,
not a new geometric coverage assertion.

`parameterIso` is the unique scheme isomorphism from the actual dynamic
centralizer scheme to the displayed Levi model, commuting with both original
inclusions into `G`. `pointHomeomorph_map_parameterIso` proves that the scheme
point map is the same as the canonical literal-subgroup identification.
`characterRestrict` pulls a literal unitary unramified character back through
these actual inclusions. Its application theorem gives the pointwise
character formula. The model's proved Laurent-coordinate theorem and the
published generic smooth-pullback theorem prove smoothness transfer.

The inducing representation `pi` remains on the literal semistandard Levi.
Its actual central subgroup `C`, quotient Haar `mu` and square-integrability
proof are displayed. `A_pi` in the Lean local notation is its pullback to
the same literal dynamic Levi through the identity on ambient points.
`characterRestrict_mem_stabilizer` proves that a self-twist of `pi` gives
an actual self-twist of its centralizer-scheme pullback. The proof uses the
published equivalence corresponding to stabilizer membership and the
actual two-pullback twisting comparison.

`orbitWeight` is only a descent utility: it descends a stabilizer-invariant
function on actual centralizer characters. Its orbit-map evaluation,
smoothness in the model coordinates and continuity are proved from the
published generic descent and smooth-pullback lemmas. This utility does not
stand in for the source density. The final `orbitPlancherelWeight` uses
precisely the published `Langlands.Plancherel.plancherelWeight` and its
proved self-twist invariance, so no arbitrary invariant weight is supplied
to that construction.

All imported conditional inputs remain visible: relative-root reflection
and central-split-torus character statements, a displayed compact open with
both parabolic factorizations, forward and reverse continuation data,
nonempty open convergence sets inside their full domains, a nonempty open
generic irreducibility locus, and regularity of the inverse canonical
composition scalar at every unitary character. These are obligations with
their existing owners; square integrability does not discharge them. No
irreducibility assumption on all tempered parabolic induction is made.

The final orbit-map evaluation gives the exact source density of the
pullback representation at the restricted character. Its smoothness and
continuity are inherited from the published actual density. The two
nonnegativity theorems retain the exact nonnegative inverse-scalar-value
premise, pointwise or on all unitary characters. They do not require or
assert strict positivity at every unitary point.

This file does not construct an orbit measure, coefficient normalization,
wave packet, weighted synthesis, global form or invariant projector. It
proves no Schwartz estimate, scalar continuation, density positivity target,
VII.2.5 isometry or VIII finiteness/inversion. Source measures, constants
and inter-parabolic normalization comparisons remain separate inputs and
obligations.
