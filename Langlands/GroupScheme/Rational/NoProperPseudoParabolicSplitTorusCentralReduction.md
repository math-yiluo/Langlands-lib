# Split tori are central modulo the radical: reduction to two inputs

Worker 1413 implemented this internal reduction for the task proving
`NoProperPseudoParabolicSolvableEnvelopeStatement`. It follows the proof of
Conrad–Gabber–Prasad, *Pseudo-reductive groups* (2nd edition, 2015),
Lemma 2.2.3, printed pp. 62–63, in the form used in the first branch of the
proof of Theorem C.2.3, printed p. 593.

`NoProperPseudoParabolicSplitTorusCentralReductionStatement` is the
conditional proposition

```text
NormalFactorFppfProductExistenceStatement →
  DynamicUnipotentUnipotenceStatement →
    NoProperPseudoParabolicSplitTorusCentralStatement.
```

All three propositions occur at the same arbitrary universe `u`. The module
proves this implication as `noProperPseudoParabolicSplitTorusCentralReduction`,
through the theorem `noProperPseudoParabolicSplitTorusCentral_of_statements`,
which takes the two inputs as explicit hypotheses and concludes the unchanged
`NoProperPseudoParabolicSplitTorusCentralStatement`. It does not prove either
input. The first input is Milne's Theorem 5.82 (the fppf product of a closed
subgroup and a normal closed subgroup is a closed subgroup); the second is
CGP Lemma 2.1.5 (`U_G(λ)` is unipotent). Their source provenance is recorded
in their own statement modules.

## Fixed data

Fix a field `k`, a smooth connected affine group scheme `G` over `Spec k`
all of whose pseudo-parabolic inclusions are isomorphisms, a unipotent radical
`r : U ⟶ G`, an fppf quotient `q : G ⟶ Q` with kernel the range of `r` and
pseudo-reductive `Q`, and a split subtorus `i : S ⟶ G`, so `S ≅ 𝔾_m^I` with `I`
finite. The goal is the published `IsCentral (i ≫ q)`.

## Helper lemmas (namespace `NoProperPseudoParabolicSplitTorusCentral`)

- `commute_of_mem_centralizer`: if a point `g` of `G` over `T` lies in the
  dynamic centralizer `Z_G(χ)` of a cocharacter `χ`, then `t ≫ χ` commutes
  with `g` for every point `t` of `𝔾_m` over `T`. The proof pulls the orbit
  equation of the published `Dynamic.mem_centralizer` back along `lift (𝟙 T) t`.

- `fppfLocallyInProduct_of_noProper` (step (a) of CGP's argument): every point
  of `G` lies fppf-locally in the product of `P_G(χ)` and the range of `r`. The
  first input, applied to the closed subgroup `Dynamic.Affine.parabolicHom χ`
  and the closed normal radical `r`, gives a closed subgroup `p : P ⟶ G`
  representing the fppf product. Since `G` is smooth, connected and affine,
  `p` satisfies the published `IsPseudoParabolicSubgroup` with the
  presentation `(U, r, χ)`, so it is an isomorphism by the hypothesis on `G`, and every
  point `x` is `(x ≫ p⁻¹) ≫ p`, which lies in the range of `p`.

- `mem_parabolic_comp_of_noProper` (step (b)): every point `y` of `Q` over `T`
  lies in `P_Q(χ ≫ q)`. Base change of `q` along `y` gives an fppf covering
  `a : W ⟶ T` and a point `x` of `G` over `W` with `a ≫ y = x ≫ q`. The
  previous lemma refines this along a further fppf covering `v` to
  `v ≫ x = p * n` with `p` in `P_G(χ)` and `n` in the range of `r`. Since the
  range of `r` is the kernel of `q`, `(v ≫ a) ≫ y = p ≫ q`, which lies in
  `P_Q(χ ≫ q)` by the published functoriality `Dynamic.parabolic_le_comap`.
  `P_Q(χ ≫ q)` is the range of the closed immersion
  `Dynamic.Affine.parabolicHom (χ ≫ q)`, so the published fppf descent of ranges
  `SubgroupFunctor.isFppfLocal_range` gives `y` in `P_Q(χ ≫ q)`.

- `mem_centralizer_of_forall_mem_parabolic` (step (c), CGP Lemma 2.2.3(2)): in
  a pseudo-reductive `Q`, if every point lies in `P_Q(ν)`, then every point lies
  in `Z_Q(ν)`. The subgroup `Dynamic.Affine.unipotentHom ν` is a closed
  subgroup; it is smooth by the published `dynamicSmooth`, connected by
  `DynamicConnected.connectedSpace_of_isRepresentedBy_unipotent`, unipotent by
  the second input, and normal because every point of `Q` lies in `P_Q(ν)` and
  `P_Q(ν)` normalizes `U_Q(ν)` (`Dynamic.conj_mem_unipotent`). The published
  `IsPseudoReductive` field `hasTrivialUnipotentRadical` makes its range
  trivial. Every point `g` of `P_Q(ν)` satisfies `g · (lim g)⁻¹ ∈ U_Q(ν)`
  (`Dynamic.mul_inv_limit_mem_unipotent`), so `g` equals its limit, which lies
  in `Z_Q(ν)` (`Dynamic.limit_mem_centralizer`).

## Main theorem

Combining the last three lemmas, for every cocharacter `ν` of `G` the image of
every point of `𝔾_m` under `ν ≫ q` commutes with every point of `Q`.

For the split torus, set `f = e⁻¹ ≫ i ≫ q : 𝔾_m^I ⟶ Q`, with `e : S ≅ 𝔾_m^I`.
For a point `z` of `𝔾_m^I` and a point `h` of `Q` over the same `T`, the
points `w` of `𝔾_m^I` with `w ≫ f` commuting with `h` form a subgroup `K`,
because `f` is a homomorphism. The published coordinate decomposition
`splitTorus.sum_proj_comp_single` together with `comp_groupHom_sum` writes `z`
as the finite product over `j ∈ I` of
`(z ≫ proj j) ≫ single j`. Each factor lies in `K`: its image under `f` is the
image of the point `z ≫ proj j` of `𝔾_m` under the cocharacter
`single j ≫ e⁻¹ ≫ i` of `G` followed by `q`. Hence `z ∈ K`, so `f` is central;
precomposing with `e.hom` (`IsCentral.comp`) gives `IsCentral (i ≫ q)`.

## Provenance

This is internal derived content: CGP prove Lemma 2.2.3 from the same two
facts (the product `P_G(λ)R_{u,k}(G)` is a closed subgroup and `U_G(λ)` is
unipotent) with the same steps. The new parts are the fppf-local formulation
of steps (a) and (b), which replaces CGP's use of the image `P_{G'}(λ')` of
`P_G(λ)` in the quotient, and the coordinate decomposition of the split torus
into its coordinate cocharacters. No imported Lean or Markdown file is changed,
and no characteristic, perfectness or reductivity hypothesis is added.
