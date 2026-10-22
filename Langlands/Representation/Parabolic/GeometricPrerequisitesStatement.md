# Actual parabolic compactness and unipotent exhaustion

Author: Worker 8. These are proposition definitions with separate proof
obligations. They neither construct the compact subgroups nor prove compactness.

Fix a prime `p`, a finite extension `F : PadicField p`, its supplied topological
realization `T`, and a positive ordered block shape `B` of total rank `n`.
All groups carry the actual topologies induced by `T.topology`.
Write `G = GL_n(F)`, `P = B.parabolic F.Carrier`, and
`N = B.unipotentRadical F.Carrier`, the normal kernel of the actual block
projection `P -> B.Levi F.Carrier`.

`ParabolicQuotientCompactClause` states compactness of the actual quotient
`P \ G`, whose points are right cosets `Pg`. `Induction.LeftQuotient` is the
quotient by the right-coset relation used for left covariance in the existing
function model; it carries the quotient topology.

`UnipotentExhaustionClause` asserts existence of a sequence `K_i` of open
subgroups of this `N`. Each underlying set is compact; the subgroups are
nested in the natural-number order; and every element of `N` belongs to
some `K_i`. No compactness of the whole radical is asserted.

`UnipotentFiniteContainmentClause` states that each finite subset of `N`
is contained in some compact open subgroup of `N`. This is exactly the
group hypothesis consumed by the published
`Langlands.SmoothCoinvariantExactnessStatement` when its ambient group is
the actual radical. It also follows from the preceding sequence assertion:
choose one index for each of the finitely many elements, take their maximum,
and use nesting. The empty finite subset can use the zeroth subgroup.

`Langlands.Parabolic.GeometricPrerequisitesStatement` conjoins these
three actual-group assertions. They are conclusions of this target,
not premises or fields inserted into the definition of a parabolic or
local field. The field universe is unrestricted; there are no representation
coefficients or module topologies in these geometric assertions.

## Original source and specialization

Casselman, *Introduction to admissible representations of p-adic groups*,
Chapter III (April 29, 2019), Section 1, page 1, explicitly uses compactness
of `P \ G` and discusses a compact open subgroup `K` with `G = P K`.
The present compactness assertion specializes that general reductive
setting to actual standard block parabolics of `GL_n` over finite
extensions of `Q_p`. It can be proved by the corresponding `GL_n`
Iwasawa decomposition or by compactness of the flag variety; neither
argument is assumed by this Lean definition.

Lemma III.3.1 and its proof, page 3, assert arbitrarily large compact open
subgroups of a p-adic unipotent group. The proof first treats upper unitriangular
matrices using conjugates by powers of a diagonal matrix built from a
uniformizer, and then takes closed subgroups. The concrete block radical is
such a closed subgroup. The sequence formulation records that explicit
construction: start with integral unitriangular matrices and conjugate by
nonnegative powers in the expanding direction. The resulting compact open
subgroups are nested, and the valuations of finitely many entries show their
union is the whole unitriangular group. Intersect them with the block radical.
This derived sequential formulation and its finite-containment consequence
are stated explicitly rather than attributed as the literal text of III.3.1.
The proof of III.3.3 on pages 3–4 uses precisely this compact detection of
finitely many coinvariant relations.

The original pages 1–4 were read. Retained source:
`casselman-2019-jacquet-module`, SHA256
`377edac998669bc88da1224c4582a173854232f7fea5caf945d140ee92fde5c1`.
Equal-characteristic local fields and general reductive groups are outside
this Lean target's scope.

The construction imports are the current Library's `Langlands.Group.GL.Blocks`,
`Langlands.Group.GL.Padic` and `Langlands.Representation.Induction.Definitions`.
The latter supplies the actual quotient convention. Worker 6 retains block
geometry ownership; this pair supplies the separate structural theorem targets
requested by that interface. It does not duplicate compact-open neighborhood
cofinality or averaging constructions. All three proof obligations remain
pending until separately proved and independently accepted.
