# Rational Howe assembly from the joint basis's reductive Levi witnesses

`Langlands.SmoothRep.rationalHoweJointAssembly` proves exactly
`Langlands.SmoothRep.RationalHoweJointAssemblyStatement.{u, v}`. This is an
internal strengthening of the seven-premise rational Howe assembly: it retains
standard cocharacters, standard Levi intersections, relative root systems,
joint special compact basis existence, cuspidal compact common-norm-kernel
coefficients and finite norm-kernel restriction for all irreducibles. The last
two premises use carrier universe `max (u + 1) v`. The proof does not assume the
separate global `StandardLeviSplitComponentStatement`.

The helper
`IsCompatibleStandardSplitComponent.standardLeviScheme_isConnectedReductive`
extracts a connected reductive representative `M` of the actual standard Levi
subgroup functor from a compatible-component witness. Both `M` and the canonical
`Standard.leviScheme` represent that same functor, so the published
`SubgroupFunctor.IsRepresentedBy.isConnectedReductive` lemma transports
connected reductivity to the canonical representative. This deduction needs no
local-field assumptions, reductivity of the ambient group or extra root-system
hypotheses beyond the compatible-component witness and the existing affine
ambient instance.

The main proof accepts the exact canonical-topology Howe target at independent
field and representation universes. It installs the rational-point local
compactness, separation and nonarchimedean instances and lifts the representation
to carrier universe `max (u + 1) v`. Actual group-algebra finite generation and
admissibility are preserved by the published lift equivalences.

After choosing a maximal split torus and a generic cocharacter, the joint basis
premise supplies one ambient special compact subgroup `K0`, its Iwasawa
products and a simultaneous basis. `commonBasisFixedGenerators` chooses a single
basis member `K` which fixes a finite generating family. This very `K` is
compact, open and normal in `K0`, its fixed vectors generate the lifted
representation, and its fixed space is finite-dimensional by admissibility.

For each irreducible actual subquotient `D`, the actual normalized Jacquet
subquotient theorem supplies a standard Levi index `I` and an irreducible
cuspidal constituent `E`. At this point the proof specializes the already
chosen ambient simultaneous basis to the root set of `I`. Its compatible
component yields connected reductivity of the canonical Levi `L` by the helper
above. The same component and the same ambient basis also remain available
for the later contraction argument. No separate global split-component
statement is introduced.

The imported `leviCompactCoefficients_of_jointBasis` helper from
`RationalHoweAssemblyProof` supplies intrinsic compact smooth-dual coefficients
for `E` on `L`'s actual common norm kernel. It applies the joint datum to `L`
itself, uses standard-family and cuspidality transport to identify all proper
normalized Jacquet tests, obtains its positive Cartan cover and applies the
cuspidal compact-restriction premise. This coefficient step may use `L`'s own
special compact subgroup.

The ambient detection argument uses the original `K` and `K0`. The selected
compatible component gives a strict element, and the simultaneous basis gives
Iwahori decomposition, contraction and cofinality for that exact `K`. The
original Iwasawa product supplies the `m * n * k` decomposition with `k` in
`K0`. The standard-cocharacter comparison identifies the literal standard
unipotent subgroup with the dynamic unipotent, whose published compact-open
containment theorem contains every finite subset in a compact open subgroup.
`rationalLeviJacquetFixedVectorDetection` combines these data with the actual
subquotients, fixed-vector generation and intrinsic compact coefficients to
produce a nonzero `K`-fixed vector of `D`. Its finite-restriction input retains
the full all-irreducibles scope of the premise, used here on `E`.

The compact-open detection consequence gives actual group-algebra finite length
of the lifted representation. The universe-lift equivalence returns finite
length of the original representation. Only the irreducible subquotient is
assumed nonzero, so the zero ambient representation is included. All field
characteristics and independent universes are retained.

This is a composition of published interfaces, with no new translation of a
literature assertion. It discharges none of the six retained prerequisites and
proves neither the unconditional Howe statement nor the general all-field
standard-Levi split-component assertion. The older seven-premise statement and
proof, the converse, the separate VI.6.3 assertions and the stronger compact-open
length bound retain their meanings and obligations.
