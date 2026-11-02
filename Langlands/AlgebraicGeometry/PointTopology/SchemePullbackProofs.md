# Compatible charts for nonaffine pullback points

Author: Worker 105. Proof of the fibre-product clause derived from
Conrad, *Weil and Grothendieck approaches to adelic points* (December 31, 2011),
Proposition 3.1, printed page 4.

For commutative rings `R` and `S` in the same arbitrary universe, with an
`R`-algebra structure on `S`, the value ring `S` carries a commutative
topological-ring structure and satisfies `IsLocalRing S` and `IsOpenUnits S`.
The schemes are arbitrary schemes over `Spec R`. Their actual relative
`S`-points carry `schemePointTopology`; the compatible-pair set carries the
subspace topology from the product of these point spaces. No finite-type or
separation assumption is used in this derived generalization of the
fibre-product clause.

`continuous_schemePullbackInverse_onChart` proves inverse continuity after
postcomposition from compatible affine charts. It constructs the actual
relative affine pullback and its map to the specified limiting cone, using
the cone's universal property. The inverse comparison equals actual
postcomposition along that map composed with the inverse affine point
homeomorphism. The equality follows by the two cone-leg identities.

`continuous_schemePullbackPointEquiv_symm` proves global inverse continuity.
At each compatible pair, choose an affine target chart containing the common
image of the value spectrum's closed point. Choose affine charts in the two
inverse images and lift the restricted maps to that target chart. The local
value-ring property makes each point factor through its chosen chart.
The common chart inclusion is monic, so the lifted pair remains compatible.
The independently defined compatible-chart map is an open embedding and the
preceding lemma proves continuity after that embedding. This gives continuity
at the original pair.

`continuous_schemePullbackPointComparison` uses continuity of the actual two
cone-leg point maps and the product subspace topology. Finally,
`schemePullbackPointHomeomorph` packages those two continuity results with
the existing actual point equivalence. Its forward map is precisely
`p ↦ (p ≫ c.fst, p ≫ c.snd)`, for any supplied limiting cone.
`schemePointPullback_proof` proves the exact Prop-valued target
`SchemePointPullbackProperty` by this homeomorphism.

The entry theorem has exactly the published `SchemePointPullbackProperty`
target. This unit supplies the arbitrary-scheme pullback comparison under the
stated value-ring hypotheses; the remaining claims of the paper are separate.
