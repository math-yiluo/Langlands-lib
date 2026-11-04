# Split tori are central modulo the radical: the smooth connected product route

Worker 1413 implemented this internal reduction for the task proving
`NoProperPseudoParabolicSolvableEnvelopeStatement`. It is a variant of the
published `NoProperPseudoParabolicSplitTorusCentralReduction`, following the
same proof of Conrad–Gabber–Prasad, *Pseudo-reductive groups* (2nd edition,
2015), Lemma 2.2.3, printed pp. 62–63, in the form used in the first branch of
the proof of Theorem C.2.3, printed p. 593. The only change is the product
input: both factors of CGP's product `P_G(λ)R_{u,k}(G)` are smooth and
connected, so the represented product is only needed for smooth connected
factors.

`NoProperPseudoParabolicSplitTorusCentralSmoothReductionStatement` is the
conditional proposition

```text
SmoothConnectedNormalFactorFppfProductExistenceStatement →
  DynamicUnipotentUnipotenceStatement →
    NoProperPseudoParabolicSplitTorusCentralStatement.
```

All three propositions occur at the same arbitrary universe `u`. The module
proves this implication as
`noProperPseudoParabolicSplitTorusCentralSmoothReduction`, through the theorem
`noProperPseudoParabolicSplitTorusCentral_of_smooth_statements`, which takes
the two inputs as explicit hypotheses and concludes the unchanged
`NoProperPseudoParabolicSplitTorusCentralStatement`. It does not prove either
input. The first input, introduced in its own statement module, is Milne's
Theorem 5.82 with Lemma 6.41 for a smooth connected closed subgroup and a
smooth connected normal closed subgroup; the second is CGP Lemma 2.1.5
(`U_G(λ)` is unipotent). Their source provenance is recorded in their own
statement modules.

## Fixed data

Fix a field `k`, a smooth connected affine group scheme `G` over `Spec k`
all of whose pseudo-parabolic inclusions are isomorphisms, a unipotent radical
`r : U ⟶ G`, an fppf quotient `q : G ⟶ Q` with kernel the range of `r` and
pseudo-reductive `Q`, and a split subtorus `i : S ⟶ G`. The goal is the
published `IsCentral (i ≫ q)`.

## Helper lemmas (namespace `NoProperPseudoParabolicSplitTorusCentralSmooth`)

- `fppfLocallyInProduct_of_noProper` (step (a) of CGP's argument): every point
  of `G` lies fppf-locally in the product of `P_G(χ)` and the range of `r`. The
  first input is applied to the closed subgroup `Dynamic.Affine.parabolicHom χ`
  and the radical `r`. The source of `parabolicHom χ` is smooth by the
  published `dynamicSmooth` and connected by the published
  `DynamicConnected.connectedSpace_of_isRepresentedBy_parabolic`, both using
  that `G` is smooth, connected and affine; the radical is closed, smooth,
  connected and normal by the fields of `IsUnipotentRadical`. The resulting
  closed subgroup `p : P ⟶ G` represents the fppf product, so it satisfies
  the published `IsPseudoParabolicSubgroup` with the presentation `(U, r, χ)`.
  It is an isomorphism by the hypothesis on `G`, and every point `x` is
  `(x ≫ p⁻¹) ≫ p`, which lies in the range of `p`. The smoothness and
  connectedness of `P` supplied by the first input are not used.

- `mem_parabolic_comp_of_fppfLocallyInProduct` (step (b)): if every point of
  `G` lies fppf-locally in the product of `P_G(χ)` and the kernel of `q`, then
  every point `y` of `Q` over `T` lies in `P_Q(χ ≫ q)`. The proof is that of
  the published `mem_parabolic_comp_of_noProper`, with the local product
  property as a hypothesis: base change of `q` along `y` gives an fppf covering
  `a : W ⟶ T` and a point `x` of `G` over `W` with `a ≫ y = x ≫ q`; a further
  fppf covering `v` gives `v ≫ x = p * n` with `p` in `P_G(χ)` and `n` in the
  kernel of `q`; so `(v ≫ a) ≫ y = p ≫ q` lies in `P_Q(χ ≫ q)` by
  `Dynamic.parabolic_le_comap`, and the fppf descent of ranges
  `SubgroupFunctor.isFppfLocal_range` for the closed immersion
  `Dynamic.Affine.parabolicHom (χ ≫ q)` gives `y` in `P_Q(χ ≫ q)`.

- `isCentral_comp_of_forall_commute`: if, for every cocharacter `ν` of `G`, the
  image of every point of `𝔾_m` under `ν ≫ q` commutes with every point of `Q`,
  then `i ≫ q` is central for every split subtorus `i`. The proof is the
  coordinate argument of the published main theorem: with `e : S ≅ 𝔾_m^I` and
  `f = e⁻¹ ≫ i ≫ q`, the points `w` of `𝔾_m^I` with `w ≫ f` commuting with a
  fixed point `h` of `Q` form a subgroup; `splitTorus.sum_proj_comp_single` and
  `comp_groupHom_sum` write a point `z` as the product over `j ∈ I` of
  `(z ≫ proj j) ≫ single j`, each of which lies in that subgroup because its
  image is the image of `z ≫ proj j` under the cocharacter
  `single j ≫ e⁻¹ ≫ i` followed by `q`. So `f` is central, and
  `IsCentral.comp` with `e.hom` gives `IsCentral (i ≫ q)`.

The published helpers `NoProperPseudoParabolicSplitTorusCentral.commute_of_mem_centralizer`
and `NoProperPseudoParabolicSplitTorusCentral.mem_centralizer_of_forall_mem_parabolic`
(step (c), CGP Lemma 2.2.3(2), which uses the second input) are reused
unchanged.

## Main theorem

For every cocharacter `ν` of `G`, the three steps give that every point of `Q`
lies in `P_Q(ν ≫ q)`, hence in `Z_Q(ν ≫ q)`, so the image of every point of
`𝔾_m` under `ν ≫ q` commutes with every point of `Q`.
`isCentral_comp_of_forall_commute` then gives `IsCentral (i ≫ q)`.

## Provenance

This is internal derived content: CGP prove Lemma 2.2.3 from the same two
facts (the product `P_G(λ)R_{u,k}(G)` is a closed subgroup and `U_G(λ)` is
unipotent) with the same steps. As in the published reduction, the new parts
are the fppf-local formulation of steps (a) and (b) and the coordinate
decomposition of the split torus; this module adds only the observation that
both product factors are smooth and connected. No imported Lean or Markdown
file is changed, and no characteristic, perfectness or reductivity hypothesis
is added.
