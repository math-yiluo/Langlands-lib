# Proof: one Levi-central element with an opposite Iwahori basis

Worker 1045 wrote this proof module and this explanation. Worker 1374
contributed the contracting point through the separate module
`Langlands.BruhatTits.Unipotent.CocharacterContraction`, which this proof
imports.

`Langlands.Aubert.General.RationalPointFamily.rationalOppositeIwahoriBasisStatement`
proves `RationalOppositeIwahoriBasisStatement.{u}` with exactly the published
type and no extra hypotheses. The module also proves the helper
`dynamic_opposite_factorization_unique`.

## Unique opposite factorization

`dynamic_opposite_factorization_unique` applies to a group scheme `G` over
a field `k` with `G.X.left` affine and `G.X.hom` separated, and to any
cocharacter `χ`. If `o * m * u = o' * m' * u'` with `o, o'` in
`U(χ⁻¹)(k)`, `m, m'` in `Z(χ)(k)` and `u, u'` in `U(χ)(k)`, then `o = o'`,
`m = m'` and `u = u'`. Here `χ⁻¹ = inverseCocharacter χ` and the subgroups
are the identity-test points of the dynamic subgroup functors.

The proof first shows that `o'⁻¹ * o = m' * u' * u⁻¹ * m⁻¹`, which lies in
`P(χ)(k)` because `Z(χ)` and `U(χ)` lie in `P(χ)`
(`Dynamic.centralizer_le_parabolic`, `Dynamic.unipotent_le_parabolic`). It
also lies in `U(χ⁻¹)(k)`. The published
`Dynamic.eq_one_of_mem_opposite_unipotent_of_mem_parabolic`
(`GroupScheme.Dynamic.OppositeIntersection`) makes it `1`, so `o = o'`.
Cancelling gives `m'⁻¹ * m = u' * u⁻¹`, an element of `Z(χ)(k) ∩ U(χ)(k)`.
`Dynamic.eq_one_of_mem_centralizer_of_mem_unipotent` makes it `1`; its
uniqueness-of-limits hypothesis is `HasLimit.unique` for the separated
`G`. Then `m = m'`, and `u = u'` by cancellation.

## The main proof

Fix the structural data of the statement: `k`, the connected reductive `G`,
the maximal split torus `i`, the canonical topology `pointTopology` on
`RationalPoint k G.X`, the three topological instances, `ν`,
`StandardCocharacterStatement`, `I`, the closedness `_hU` of
`unipotent i ν I`, and the standard cocharacter witness `ζ`. From `hG` the
proof obtains that `G.X.hom` is smooth, affine and separated, and that
`G.X.left` is affine. `Langlands.BruhatTits.localField_t2Space` makes `k`
Hausdorff.

Let `χ = CommGroupScheme.groupHom ζ ≫ i`. Applying the given
`StandardCocharacterStatement` to `rootSet i ν I` and the witness `ζ`
gives `standardLevi i ν (rootSet i ν I) = Z(χ)` and
`standardUnipotent i ν (rootSet i ν I) = U(χ)`. Hence, on rational points,

- `M = levi i ν I` equals `Z(χ)(k)`,
- `U = unipotent i ν I` equals `U(χ)(k)`,
- `O = oppositeUnipotent i ζ` equals `U(χ⁻¹)(k)` by definition.

The element. Worker 1374's
`BruhatTits.DynamicUnipotentContainment.exists_central_contractingPoint`,
applied to `χ`, gives one rational point `g`. This `g` lies in `Z(χ)(k)` and
commutes with every element of `Z(χ)(k)`. For every compact subset of
`U(χ)(k)`, the conjugates by `g ^ n` tend to `1` uniformly. For every compact
subset of `U(χ⁻¹)(k)`, the conjugates by `(g ^ n)⁻¹` do the same. All of this
is for the canonical `rationalPointTopology`. The
construction takes `g = χ(t)` for a unit `t` whose powers tend to `0`. The
first conclusion of the statement, `m * g = g * m` for `m ∈ M`, is this
commutation after rewriting `M = Z(χ)(k)`.

The basis. After rewriting `M`, `U` and `O`, the proof applies
`Jacquet.hasOppositeIwahoriContractionBasis_of_contraction` from
`Representation.Jacquet.OppositeIwahoriBasisAbstract` with these inputs:

- closedness of `O`: the published `isClosed_oppositeUnipotent_localField`;
- closedness of `U`: the statement's hypothesis `_hU`;
- `g ∈ M`, centrality of `g` in `M`, and both uniform contractions: from
  `exists_central_contractingPoint`;
- `M` normalizes `U`: `Dynamic.centralizer_le_normalizer_unipotent`;
- `M` normalizes `O`: the same lemma for `χ⁻¹`, after the published
  `Dynamic.centralizer_inverseCocharacter` identifies `Z(χ⁻¹)` with `Z(χ)`;
- unique factorization: `dynamic_opposite_factorization_unique χ`;
- the open cell condition: `Dynamic.opposite_cell_mem_nhds_one` from
  `GroupScheme.Dynamic.RationalOpenCell`, after
  `rationalPointTopology_eq_rationalSchemeTopology` replaces the canonical
  topology by the scheme-chart topology used there.

The abstract criterion uses the statement's `LocallyCompactSpace` and
`NonarchimedeanGroup` instances. It does not use `T2Space` of the group.
It returns `Jacquet.HasOppositeIwahoriContractionBasis U M O g` for the
chosen `g`, which is the second conclusion.

The proof makes no case split on `I`, the root data or the
characteristic. It uses no root-system, Willis-theory or
special-compact-subgroup input.

## Provenance

The mathematical background for the statement is Bill Casselman,
*Introduction to admissible representations of p-adic groups*, Chapter III
(registered as `casselman-2019-jacquet-module`), Section III.4. The open
cell input is the published `OppositeCellStatement`, citing
Conrad–Gabber–Prasad, Proposition 2.1.8(3), and Conrad, *Reductive group
schemes*, Theorem 4.1.7(4). The route above follows neither text. It
combines the published Library results named here with the internal
modules `OppositeIwahoriBasisAbstract`, `RationalSchemePoints`,
`RationalOpenCell` and Worker 1374's `CocharacterContraction`.
