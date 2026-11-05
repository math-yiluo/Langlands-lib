# The underlying relative identity set and the all-test criterion

For an actual group scheme `G` over any scheme `S`, `underlyingSet G` is the
union, in the underlying topological space of `G`, of the identity connected
components of all its residue fibres. The projection of each actual residue
fibre is the Mathlib map `G.X.hom.fiberι s`.

This is the set in SGA 3, Exposé VI_B, special case 3.4, PDF page 18 / printed
page 348, in the Gille–Polo recomposed edition of 13 October 2024 (registered
source `sga3-expose-vib-gille-polo-2024`, SHA-256
`88d8ccb045fc959535155eb4b0fc72e3e4845730fb73355f2043e8023b7db3d2`).
The official one-page errata `sga3-tome1-errata-gille-polo-2024`, SHA-256
`e17b90eac75b25f53b5a6f7be84450b71c2f0d7df98f5c9f4ad4cb8e9038cea7`,
has no correction to this passage. Both passages were read locally.

The implemented proof uses Mathlib's homeomorphism of the scheme-theoretic
residue fibre with the topological fibre. The projection is injective and its
image lies over the indexing point. Thus membership of a projected fibre point
in `underlyingSet G` is equivalent to membership of the original point in that
fibre's identity component (`fiberι_mem_underlyingSet_iff`).

`inRelativeIdentityComponent_iff_range_subset` proves that the published
all-test membership criterion is equivalent to the entire topological image
of the test map lying in `underlyingSet G`. For the forward implication, lift
each source point to its own residue fibre using `Scheme.Hom.asFiber`, and
apply the all-test hypothesis there. For the reverse implication, the
pullback map commutes with the fibre projections, so every image point in
the target fibre projects into the union; the previous equivalence applies.
`factors_iff_range_subset` combines this result with the published
representation predicate for any supplied open representative.

All schemes, residue fields and test schemes share an arbitrary universe `u`.
There is no smoothness, affineness, reducedness or finiteness hypothesis. Tests
can be nonaffine or nonreduced. This unit does not prove openness of the union,
construct its group law, prove existence of a representative, establish
geometric connectedness or normality, or prove arbitrary-base-change
compatibility. Those are the remaining obligations of the smooth structure
proof task.
