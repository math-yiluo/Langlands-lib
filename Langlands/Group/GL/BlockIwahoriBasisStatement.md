# Cofinal compact open block Iwahori factorization

Author: Worker 117.

## Exact statement

`Langlands.GeneralLinear.BlockShape.BlockIwahoriBasisStatement` is a transparent
Prop-valued definition. Its parameters are an arbitrary prime `p`, an arbitrary
finite p-adic field `F : PadicField.{uF} p`, a natural rank `n`, an ordered block
shape `B : GeneralLinear.BlockShape n`, and supplied `T : F.TopologicalData`.
The explicit arguments are `B` and `T`; `p`, `F`, and `n` are implicit, with
`Fact p.Prime` a typeclass argument.

The definition installs exactly `T.topology` on `F.Carrier`. The resulting
topology on the actual `GeneralLinear n F.Carrier` is the induced matrix-unit
topology, definitionally the topology called `T.generalLinearTopology n` by
the existing p-adic GL API. The neighborhood filter, open subgroups, compactness,
and factorization predicate all use this same supplied topology.

For every set `U` belonging to the ambient identity-neighborhood filter, the
statement asserts the existence of an actual
`K : OpenSubgroup (GeneralLinear n F.Carrier)` such that:

1. Its underlying subset of the ambient GL is compact.
2. That subset is contained in `U`.
3. `B.HasBlockIwahoriFactorization T K` holds.

The last conjunct uses the published predicate unchanged. Its factors are the
actual intersections of `K` with the opposite unipotent subgroup, embedded
common Levi, and upper unipotent subgroup. Their ordered multiplication
`(l,m,u) ↦ l*m*u` is required to be bijective onto `K`. For every scalar tuple
`a : Fin B.length → F.Carrierˣ` satisfying `B.IsWeaklyContracting T a`, forward
conjugation by `B.blockScalar F.Carrier a` preserves `K ∩ N` by containment,
and inverse conjugation preserves `K ∩ Nop` by containment.

All natural ranks, including zero, and all existing block shapes are retained.
There is no positivity premise on `n` or nonempty-shape premise. For empty or
one-block shapes there are no pairs of block indices `i < j`, so the scalar
inequalities are vacuous. No additional field realization, local compactness,
representation, or factorization witness is assumed.

## Provenance and weak-chamber strengthening

The source is Bill Casselman, *Introduction to admissible representations of
p-adic groups*, Chapter III: *Induced representations and the Jacquet module*,
revision April 29, 2019, section 4, page 5: the definition of Iwahori
factorization and Lemma III.4.1, including its congruence-subgroup discussion.
The registered source is `casselman-2019-jacquet-module`, SHA256
`377edac998669bc88da1224c4582a173854232f7fea5caf945d140ee92fde5c1`.

Casselman's definition uses the strict chamber `A_P^{--}`. The present target
is a concrete derived strengthening in the containment condition: for every
forward pair `i < j`, it allows the normalized absolute value of `a_i/a_j`
to be at most one, including equality, rather than requiring it to be less
than one. It keeps the source's lower-Levi-upper multiplication order.
Strict contraction implies weak contraction, so the requested containments
include the strict-chamber ones. This stronger existence statement is not
claimed to follow literally from the cited general lemma.

The intended additional justification is entrywise integral/congruence control
for actual GL. The published `blockScalar_conj_apply` multiplies the upper
`(i,j)` block by `a_i/a_j`; `blockScalar_inv_conj_apply` multiplies the lower
`(j,i)` block by the same ratio. A ratio of normalized absolute value at most
one is integral and preserves each congruence ideal under multiplication,
including at equality. This explains the proposed weak-chamber extension for
principal congruence subgroups. Establishing such subgroups, their factorization,
and their cofinality in the supplied topology is a separate proof obligation.

The imported `Langlands.Group.GL.CompactOpen` already supplies compact open
subgroups inside identity neighborhoods, with the actual supplied topology
and no extra local compactness hypothesis. That result does not provide the
factorization or weak-chamber invariance required here.

This module states the cofinal existence target only; it proves no existence
theorem. It chooses no tower or congruence level and asserts no normality,
simultaneous compatibility for all parabolics, contraction convergence,
averaging, canonical lifts, admissibility, or pairing result. Casselman's
additional normality and smaller-parabolic compatibility clauses are outside
this focused statement.
