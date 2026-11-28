# The opposite cell on points with values in a local topological ring

Module `Langlands.GroupScheme.Dynamic.RingPointOpenCell`, namespace
`Langlands.GroupScheme.Dynamic`.

## Statement

Let `k` be a field, `G` a group scheme over `Spec k` and `χ : 𝔾_m → G` a cocharacter. Write
`χ⁻¹` for `χ` precomposed with the power map `t ↦ t⁻¹` (`Gm.powerHom _ (-1)`), and `U(χ)`,
`Z(χ)`, `P(χ)` for the dynamic unipotent subgroup, centralizer and parabolic
(`Dynamic.unipotent`, `Dynamic.centralizer`, `Dynamic.parabolic`). Let `S` be a commutative
`k`-algebra which is a local ring and a topological ring with open units (`IsOpenUnits S`), for
example the completion of a number field at an archimedean place.

`affinePoints_opposite_cell_mem_nhds_one`: if `G` is smooth, affine and separated over `k`, then
for all identity neighborhoods `A`, `B`, `C` of `G(S) = G.affinePoints (CommAlgCat.of k S)`, with
its regular-function evaluation topology, the set of products `a b c` with
`a ∈ A ∩ U(χ⁻¹)(S)`, `b ∈ B ∩ Z(χ)(S)` and `c ∈ C ∩ U(χ)(S)` is an identity neighborhood of
`G(S)`. Here `U(χ⁻¹)(S)` is the carrier of the subgroup functor on the test scheme `Spec S`.

The points are points of `G` itself over the `k`-algebra `S`; no base change of `G` to `S` is
made. For `S = k` this is the rational-point statement `opposite_cell_mem_nhds_one` of the module
`Langlands.GroupScheme.Dynamic.RationalOpenCell`, whose proof is followed here.

## Proof

- `cell_point_decomposition_test` is the decomposition `cell_point_decomposition` of
  `RationalOpenCell` for points over an arbitrary test scheme `Y` instead of `Spec k`, with the
  same proof. Let `iO : O → G` represent `U(χ')`, `iP : P → G` be a homomorphism and `L` a limit,
  for `χ`, of the universal point of `P`. A point `w` of `O × P` over `Y` gives
  `o = w ≫ fst ≫ iO ∈ U(χ')(Y)`, `l = w ≫ snd ≫ L ∈ Z(χ)(Y)` and `l⁻¹ (w ≫ snd ≫ iP) ∈ U(χ)(Y)`,
  and the image of `w` under the multiplication `O × P → G` is their product.
- `ringCell_mem_nhds_one_of_isOpenImmersion`: if `iP` represents `P(χ)` and the multiplication
  `O × P → G` is an open immersion, the cell statement holds on `S`-points for the scheme-point
  topology `schemePointTopology k _ S`. The three maps `w ↦ o`, `w ↦ l`, `w ↦ l⁻¹ p` on `S`-points
  of `O × P` are continuous (`schemePointContinuity_proof`) and send `e = (1, 1)` to `1` (for `l`
  by uniqueness of limits), so the preimage `W` of `A × B × C` is a neighborhood of `e`. Open
  immersions give open embeddings on `S`-points for local `S` with open units
  (`isOpenEmbedding_schemePointMap`), so the image of `W` is an identity neighborhood, and each of
  its points is a product of the required form.
- `affinePoints_opposite_cell_mem_nhds_one` applies this with the affine representatives
  `Affine.unipotentHom` and `Affine.parabolicHom` and the published open immersion
  `oppositeCellStatement` (`GroupScheme.Absolute.OppositeCellProof`, Conrad–Gabber–Prasad,
  *Pseudo-reductive groups*, Proposition 2.1.8(3)). The evaluation topology on
  `G.affinePoints (CommAlgCat.of k S)` and the scheme-point topology agree: the identity map is
  the homeomorphism `affinePointsRingPointHomeomorph`, and `schemePointTopology_eq_affine`
  identifies the scheme-point topology of an affine scheme with its evaluation topology.

The module uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.
