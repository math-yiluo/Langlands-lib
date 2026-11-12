# Stabilizers of unipotent actions with constant orbit dimension are smooth

Author: Worker 79.

`UnipotentOrbitStabilizerSmoothStatement` states that, in characteristic zero, the
stabilizer scheme of a unipotent group acting on a reduced scheme with constant orbit
dimension is smooth over that scheme. This is the flatness of the stabilizer asserted in
Conrad's Example 5.5, in a stronger form, proved through Cartier's theorem rather than
Conrad's `exp(ker B)` description. The module states the claim and contains no proof.

## The statement

Notation is that of `UnipotentOrbitQuotientStatement.lean`. Let `k : Type u` be a field of
characteristic zero (`CharZero k`) and `G : GroupScheme (Spec k)` a group scheme with:

- `IsAffineHom G.X.hom` and `LocallyOfFiniteType G.X.hom`: `G` is affine and locally of
  finite type, hence of finite type, over `k`;
- `IsUnipotent G` (`Langlands/GroupScheme/Reductive/Basic.lean`): every nonzero
  finite-dimensional matrix representation of `G` has a nonzero fixed vector.

These three conditions are `IsUnipotentAlgebraicGroup k G` of the target module, written
out because that predicate is stated over a normed field. Let `Z : Over (Spec k)` be a
reduced scheme (`IsReduced Z.left`) locally of finite type over `k`, let
`b : SchemeAction G Z` be an action and let `d : ℕ`. Assume
`HasOrbitDimension b z d` for every point `z` of `Z`: the dimension of `G` equals `d` plus
the dimension of the stabilizer of `z`, the fibre over `z` of the stabilizer scheme.

The conclusion is that the projection to `Z` of the stabilizer scheme,
`pullback.snd (lift b.hom (snd G.X Z)) (lift (𝟙 Z) (𝟙 Z))`, is smooth. This is the base
change of the action graph `(g, z) ↦ (g.z, z)` along the diagonal of `Z`, the morphism
whose flatness is `IsStabilizerFlat b`. Smooth morphisms are flat, so the conclusion gives
`IsStabilizerFlat b`.

## Sources

- Brian Conrad, *Weil and Grothendieck approaches to adelic points* (December 31, 2011),
  registered source `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
  `fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`, Example 5.5,
  printed p.16: "The universal action map `G × V_d → V_d × V_d` defined by
  `(g, v) ↦ (g.v, v)` is flat over the diagonal (since the stabilizer scheme in the
  `V`-group `G × V` is `exp_{(G×V)/V}(ker B)` for the differentiated vector bundle map
  `B : g × V → Tan_{V/k}` over `V`, and `ker B` is a subbundle over `V_d` due to `B`
  having constant rank over `V_d`)." Here `Z` plays the role of `V_d`.
- J.-E. Bertin, SGA 3, Exposé VI_B, recomposed edition by P. Gille and P. Polo
  (13 October 2024), registered source `sga3-expose-vib-gille-polo-2024`, SHA-256
  `88d8ccb045fc959535155eb4b0fc72e3e4845730fb73355f2043e8023b7db3d2`, Corollaire 4.4,
  printed p.354 (PDF p.24). For an `S`-group `H` locally of finite presentation along
  the unit section, condition (ii) is "pour tout `s ∈ S`, `H_s` est lisse sur `κ(s)`, et
  la fonction `s ↦ dim H_s` est localement constante sur `S`". The corollary continues:
  "Si on suppose de plus `S` réduit, alors les conditions (i) à (iv) sont équivalentes,
  et impliquent que `H⁰` est lisse sur `S`." Here `H⁰` is the open subgroup formed by the
  identity components of the fibres.
- J. S. Milne, *Algebraic Groups* (2022 corrected reprint), registered source
  `milne-2022-algebraic-groups`, SHA-256
  `f2ddd8fa4d263085f173934664b246007a2c0bd539739b7c82de39bfb5d21f40`: Theorem 3.23
  (Cartier), printed p.71, "Every affine algebraic group over a field of characteristic
  zero is smooth"; Proposition 1.41, printed p.19, algebraic subgroups are closed
  subschemes; Corollary 14.7, printed p.282, subgroups of unipotent algebraic groups are
  unipotent; Corollary 14.9, printed p.282, unipotence is invariant under extension of
  the base field; Corollary 14.15, printed p.283, a unipotent algebraic group "is
  connected if `k` has characteristic zero".

## Derivation (provenance: derived)

The statement combines these results; it is not stated in this form in a source. Let
`H → Z` be the stabilizer scheme, a group scheme over `Z`.

1. `H → Z` is locally of finite type, being the composite of a base change of the
   diagonal of `Z` (an immersion) with the projection `G × Z → Z`. As `Z` is locally
   Noetherian, it is locally of finite presentation.
2. For a point `z`, the fibre `H_z` is the subgroup scheme `{g | g.z = z}` of
   `G_{κ(z)}`. Its map to `G_{κ(z)}` is a base change of the diagonal of `Z`, an
   immersion, so `H_z` is an algebraic subgroup, closed by Milne, Proposition 1.41,
   printed p.19, and affine. By Milne 14.9 and 14.7 it is a unipotent algebraic group
   over `κ(z)`, so it is connected (14.15) and smooth (3.23), since `κ(z)` has
   characteristic zero.
3. `G` is of finite type over `k`, so its dimension is a natural number `n`, and
   `HasOrbitDimension b z d` makes `dim H_z = n - d` for every `z`. So the fibre
   dimension is constant.
4. By (1)–(3), condition (ii) of SGA 3 VI_B 4.4 holds. As `Z` is reduced, `H⁰` is smooth
   over `Z`. The fibres of `H` are connected (step 2), so `H⁰ = H`, and `H → Z` is smooth.

Reducedness of `Z` cannot be dropped: Note (31) of the recomposed edition, on the same
page, gives a non-flat group over `k[δ]/(δ²)` satisfying (ii). Connectedness of the
fibres is needed for `H⁰ = H`. The names of the declarations are derived here.
