# Canonical point neighbourhoods from finite ordered products

Worker 384, with the consumer interface proposed by Worker 1605.

This internal topology helper supports the proof of KP Corollary 8.2.6. It is
derived from the Library's actual finite scheme products, represented subgroup
point equivalences and continuity of morphisms on affine rational points. It
does not assert an unconditional root-product decomposition.

`exists_open_restrict_subgroup` extracts an ambient open identity neighbourhood
from a subgroup open in the subspace topology of another subgroup. It requires
no topological group structure.

`orderedProductIso_inv_one` considers an isomorphism from a finite product of
group schemes to a group scheme whose inclusion in an ambient group is a
monomorphism. If this isomorphism followed by the inclusion is the actual
ordered multiplication map, its inverse sends the identity point to the
product identity, over every test scheme. The proof evaluates ordered
multiplication at the product identity and cancels the monomorphism.

`exists_open_restrict_orderedProduct` works over any topological commutative ring
`F` in arbitrary universe `u`. The ambient group scheme `G` is affine, `jU`
is a closed representative of `RU`, and the finite family `j r` represents
the actual subgroup functors `R r`. The same compatible ordered-product
isomorphism is supplied. Given subgroups `V r` open in the actual carriers
`R r(F)` and contained in an ambient subgroup `K`, it constructs an open
identity neighbourhood `C` in `G(F)` for which `C ∩ RU(F)` is contained in `K`.
The factor inclusions need not be closed: their representability is enough.

`OrderedProductNeighborhoodStatement` packages this complete conditional
assertion as a proposition, universally quantifying the topological ring,
group schemes, representatives and compatible product isomorphism.
`orderedProductNeighborhood` proves that proposition by the preceding
construction. Every structural premise remains explicit, including the
closedness of the product subgroup representative and the ordered-product
isomorphism. The original callable helper retains its full interface.

All point spaces use the actual identity-test convention. The ambient topology
is exactly `rationalPointTopology F G.X`, and each factor carrier has its
subspace topology. The proof first extends each subspace-open `V r` to an
ambient open set `O r`. The representative `U` is affine because `jU` is a
closed immersion into the affine scheme `G`. Each inverse coordinate followed
by its factor inclusion is an actual scheme morphism
`U.X → G.X`. Its point map is continuous for the two canonical
`rationalPointTopology` topologies by `continuous_rationalPointMap`. The finite
intersection of its inverse images of the `O r` is therefore open in `U(F)`.
The preceding identity lemma shows that this intersection contains the identity.
`isEmbedding_rationalPointMap` for the closed inclusion `jU` extends it to
an ambient open set `C`. Finally, the ordered point-product formula expresses
each point in `C ∩ RU(F)` as a product of elements of `K`.

No topology on the finite scheme product is introduced, and no comparison
with the scheme-chart topology is used. The only representative-to-subspace
comparison is the published embedding theorem for `jU`, for exactly the named
canonical topologies.

The intended application is the neighbourhood step in Kaletha–Prasad,
*Bruhat–Tits Theory: A New Approach* (2023), Corollary 8.2.6, printed p.291 /
PDF p.322, registered source
`kaletha-prasad-2023-bruhat-tits-new-approach`. The adjacent proof of
Theorem 8.2.5 uses ordered root products and the opposite open cell.
The authors' 1 November 2024 corrections, source
`kaletha-prasad-2024-corrections`, PDF pp.37–38, do not alter these two results.
The helper's proof is an internal derivation of the necessary point-topology
step. It leaves the existence of the scheme product isomorphism and the final
open-cell assembly as separate obligations.
