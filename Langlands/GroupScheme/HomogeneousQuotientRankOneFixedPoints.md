# Fixed points of a prescribed homogeneous quotient in rank at most one

Author: Worker 1547.

This internal module bounds the all-test torus-fixed rational points of a
supplied homogeneous quotient by a prescribed subgroup. It also records the
elementary implication from a geometric fixed-point lower bound to quotient
dimension at most one. The geometric lower bound remains an explicit input.

Over an algebraically closed field `k : Type u` of any characteristic, let `G`
be connected reductive and `i : T → G` a split maximal torus. Assume every pair
of actual roots is integrally linearly dependent. Let `b : B → G` be any actual
closed subgroup, with an actual torus factor `t : T → B` satisfying `t ≫ b = i`.
Retain the hypotheses `MaximalToriAreConjugate B` and that the whole-torus
centralizer's rational points belong to the range of `b`.

The supplied map `q : G → Q` is flat, surjective and quasi-compact, with its
fibers on every relative scheme test exactly the right cosets of the range of
`b`. No smoothness, properness or finite-type condition on `Q` is supplied.
The subgroup is prescribed; it need not be presented as a dynamic parabolic,
nor is a cocharacter chosen.

`HomogeneousQuotient.rankOneFixedPointSignEmbedding` constructs an injection
into `Bool` from the rational points of `Q` fixed on every scheme test by the
canonical quotient action restricted along `i`. This is fixedness under the
whole group scheme after every test change, including nonreduced tests.

The proof first lifts every rational quotient point to `G`. Reductive
smoothness gives local finite type of `G`, hence of `q` by its structure-map
equation. Surjectivity of `q` and the published rational-lift theorem over an
algebraically closed field then supply actual rational lifts over `Spec k`.
The canonical quotient action on these lifts is multiplication followed by
`q`. The published `torusFixedPointWeylEmbedding` uses the actual torus
factor, conjugacy inside `B`, centralizer containment and rational lifting to
embed fixed points into `N_G(T)(k)/Z_G(T)(k)`. Composing with the published
rank-one relative Weyl sign embedding gives the claimed injection into `Bool`.
`finite_rankOneFixedPoints` and `card_rankOneFixedPoints_le_two` respectively
deduce finiteness and the `Nat.card` bound of two from that injection.

`SchemeAction.topologicalKrullDim_le_one_of_fixedPointSignEmbedding` is a
general elementary consumer for any group-scheme action over any field in
universe `u`. It takes an injection of all-test fixed rational points into
`Bool` and the implication that topological Krull dimension at least two
supplies an injection from `Fin 3` into those fixed points. If dimension
exceeded one, the successor-order law in `WithBot ℕ∞` would give dimension at
least two. Composing the two injections would force `3 ≤ 2`, a contradiction.
Thus the actual topological Krull dimension is at most one, including when the
dimension could initially be infinite. The argument does not infer a cardinal
lower bound from `Nat.card` for a potentially infinite type.

`HomogeneousQuotient.dimension_le_one_of_three_fixedPoints` applies this
elementary consumer to the constructed prescribed-quotient sign embedding.
Its three-fixed-point implication remains explicit. In particular, this
module does not prove the projective torus fixed-point dimension theorem that
would supply that implication. It does not construct a quotient, prove its
properness, establish torus conjugacy or centralizer containment, or prove
the unconditional positive-root uniqueness statement.

The provenance is internal composition of the published fixed-coset,
rank-one Weyl, rational-lifting and canonical-action results, followed by
finite-set counting and extended-natural successor-order arithmetic. It
generalizes the fixed-point bound for a represented dynamic parabolic in
`Dynamic.RankOneFixedCosetBound` by exposing the actual subgroup factor and
centralizer-containment hypotheses that that earlier specialization derives
from its dynamic presentation.
