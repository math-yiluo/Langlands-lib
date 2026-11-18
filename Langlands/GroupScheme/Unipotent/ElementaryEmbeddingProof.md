# Smooth commutative groups of exponent `p` are elementary unipotent

`Langlands.GroupScheme.smoothExponentElementaryUnipotent.{u}` proves the
published `Langlands.GroupScheme.SmoothExponentElementaryUnipotentStatement.{u}`.
This is Proposition 14.49 of James S. Milne, *Algebraic Groups* (2017),
printed p. 296 (PDF p. 312), with elementary unipotence as in Definition 14.45
on printed p. 295. The registered source is `milne-2017-algebraic-groups`,
SHA-256 `899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.

The proof bundles the given group and its commutativity instance as a
`CommGroupScheme`. Forgetting commutativity recovers the original group, so
the smoothness, affineness and exponent on every relative scheme test apply
directly to the published `RelativeRoot.smoothCommutativePTorsionVectorEmbedding`
(the embedding assertion of Conrad–Gabber–Prasad, Lemma B.1.10). That theorem
constructs a closed embedding `i : G ⟶ V` over `k`, where `V` has natural
additive coordinates of some finite dimension `n` on all tests. Its proof
uses primitive generators of the coordinate Hopf algebra.

`RelativeRoot.IsVectorGroupOfDimension.iso` turns those coordinates into an
actual group-scheme isomorphism `e : V ≅ VectorGroup.groupScheme (CommRingCat.of k) n`.
The witness is `i ≫ e.hom`, which is a closed immersion by
`IsClosedSubgroup.comp_iso`. This works in every universe over arbitrary
fields of characteristic `p`, including imperfect fields and disconnected
source groups.
