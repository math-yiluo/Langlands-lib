# The rational opposite cell is an identity neighborhood

Worker 1045 wrote this module and this explanation. It turns the published
scheme-theoretic opposite open cell into a statement about rational points.
Let `k` be a field with a topology making it a topological ring with open
units (`IsOpenUnits k`). Let `G` be a group scheme over `Spec k` and
`χ : 𝔾_m ⟶ G` a cocharacter. Write `U(χ)`, `Z(χ)` and `P(χ)` for the dynamic
unipotent subgroup, centralizer and parabolic, and `U(χ)(k)` etc. for their
identity-test points.

## Main result

`Langlands.GroupScheme.Dynamic.opposite_cell_mem_nhds_one` assumes that
`G.X.hom` is smooth, affine and separated. Let `χ⁻¹` be the composite of `χ`
with the power map `t ↦ t⁻¹`, exactly as in `OppositeCellStatement`. Give
`G(k)` the scheme-chart topology `rationalSchemeTopology k G.X`. Then for
any identity neighborhoods `A`, `B` and `C` of `G(k)`, the set of products
`a * b * c` with `a ∈ A ∩ U(χ⁻¹)(k)`, `b ∈ B ∩ Z(χ)(k)` and
`c ∈ C ∩ U(χ)(k)` is an identity neighborhood.

Only the scheme-chart topology on `G(k)` occurs in the statement. If `G.X`
is affine, `rationalPointTopology_eq_rationalSchemeTopology` identifies it
with the canonical `rationalPointTopology`; the final proof uses that
identification.

## Proof

`cell_point_decomposition` assumes only that `G.X.hom` is separated. Let
`iO : O ⟶ G` represent `U(χ')` for any cocharacter `χ'`, let `iP : P ⟶ G` be
a homomorphism, and let `L : P.X ⟶ G.X` be a limit, for `χ`, of the
universal point `iP.hom.hom`. For each rational point `w` of `O.X ⊗ P.X`,
write `o = w ≫ fst ≫ iO`, `p = w ≫ snd ≫ iP` and `l = w ≫ snd ≫ L`. Then:

- `o ∈ U(χ')(k)`, by representability of `U(χ')`;
- `l` is a limit of `p` (`HasLimit.comp` from `Dynamic.LimitMap`), so
  `l ∈ Z(χ)(k)` (`HasLimit.mem_centralizer`);
- `p * l⁻¹ ∈ U(χ)(k)` (`HasLimit.mul` and `hasLimit_of_mem_centralizer`),
  hence `l⁻¹ * p ∈ U(χ)(k)`, because `Z(χ)(k)` normalizes `U(χ)(k)`
  (`centralizer_le_normalizer_unipotent`);
- the image of `w` under the multiplication morphism `o * p` equals
  `o * l * (l⁻¹ * p)`.

`cell_mem_nhds_one_of_isOpenImmersion` assumes in addition that `iP`
represents `P(χ)` and that the multiplication morphism `O × P ⟶ G` is an
open immersion. Since `iP.hom.hom` itself is a point of `P(χ)`,
`exists_hasLimit` from `Dynamic.Decomposition` supplies `L`. At the point
`e = lift 1 1`, the three maps `w ↦ o`, `w ↦ l` and `w ↦ l⁻¹ * p` all take
the value `1`. For `l` this follows from uniqueness of limits
(`HasLimit.unique`). These maps are continuous for the scheme-chart
topologies (`continuous_rationalSchemePointMap`). So the preimage `W` of `A`,
`B`, `C` under them is a neighborhood of `e`. The multiplication map is an
open embedding on rational points (`isOpenEmbedding_rationalSchemePointMap`),
so the image of `W` is a neighborhood of `1`. By the decomposition, every
point of this image is a product of the required form.

`opposite_cell_mem_nhds_one` applies this with the published affine
representatives `Affine.unipotentHom` and `Affine.parabolicHom` from
`Dynamic.AffineRepresentability`. The open immersion hypothesis is the
published theorem `oppositeCellStatement` from
`GroupScheme.Absolute.OppositeCellProof`.

## Provenance

The scheme-level input is `OppositeCellStatement`, which cites
Conrad–Gabber–Prasad, *Pseudo-reductive groups*, Proposition 2.1.8(3), and
Conrad, *Reductive group schemes*, Theorem 4.1.7(4). The passage to rational
points and identity neighborhoods is an internal derivation using the
published Library results named above.
