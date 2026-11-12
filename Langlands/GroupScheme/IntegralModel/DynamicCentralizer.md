# Integral centralizer models and Levi maximality from a torus special centralizer

All rings and schemes use one arbitrary universe `u`. This module builds a
supplied-model version of the dynamic centralizer of an integral cocharacter, and
proves maximality of integral points on the centralizer of the generic
cocharacter, conditional on two explicit hypotheses: the special fibre of the
integral centralizer is a torus, and the integral points of the ambient model are
open.

## Integral points through a closed model morphism

Let `R` be a domain with specified fraction field `K`, `M : IntegralModel R K G`
and `Z : IntegralModel R K P` supplied models, `p : P ⟶ G` a homomorphism of
generic groups, and `φ : Z.Hom M p` a model morphism over `p` (the Library
structure `IntegralModel.Hom`). `Hom.mem_integralPoints_of_map_mem` assumes that
`φ.hom : Z.group ⟶ M.group` is a closed subgroup (`IsClosedSubgroup`). If a
rational point `ℓ` of `P` has `rationalPoints.map p ℓ ∈ M.integralPoints`, then
`ℓ ∈ Z.integralPoints`. The proof moves `ℓ` to the generic fibre of `Z.group` with
the inverse generic identification of `Z`. By the compatibility square of `φ`, its
image under the generic fibre of `φ.hom`, followed by the generic identification
of `M`, is `rationalPoints.map p ℓ`. The published
`exists_eq_of_integralPointMap_eq` then gives an integral section of `Z.group`
restricting to that generic point, and so `ℓ` is in the image of the integral
sections of `Z`.

## The integral dynamic centralizer as a model

In the namespace `DynamicCentralizer`, fix `M : IntegralModel R K G`, a
cocharacter `χ : Gm(Spec R) ⟶ M.group`, and a closed subgroup `p : P ⟶ G` whose
range, read in the generic fibre of the model through `M.genericIso.inv`, is the
dynamic centralizer of the base-changed cocharacter:

```text
range (p ≫ M.genericIso.inv)
  = Dynamic.centralizer (Dynamic.baseChangeCocharacter (Spec.algebraMap R K) χ).
```

This is an equality of subgroup functors on all schemes over `Spec K`.

- `isRepresentedBy_generic` records that `p ≫ M.genericIso.inv` represents that
  centralizer.
- `genericIso` is the isomorphism from the generic fibre of the Library centralizer
  scheme `Dynamic.Affine.centralizerScheme χ` to `P`. Base change of the centralizer
  inclusion represents the base-changed centralizer
  (`Dynamic.isRepresentedBy_centralizer_baseChange`), and two representatives of
  one subgroup functor are isomorphic (`isoOfIsRepresentedBy`).
- `genericIso_hom_comp` states that this isomorphism followed by `p` equals the
  generic fibre of `Dynamic.Affine.centralizerHom χ` followed by `M.genericIso.hom`.
- Assuming `M.group` is smooth over `Spec R`, `model` is the
  `IntegralModel R K P` with group `Dynamic.Affine.centralizerScheme χ` and generic
  identification `genericIso`. It is affine because the centralizer inclusion is a
  closed immersion into an affine group, and flat and locally of finite type
  because the centralizer is smooth over any base ring when the ambient group is
  (`Dynamic.smooth_affineCentralizer_overRing`).
- `inclusion` is the model morphism `model ⟶ M` over `p` given by
  `Dynamic.Affine.centralizerHom χ`; `isClosedSubgroup_inclusion` records that it
  is a closed subgroup.

This mirrors the published parabolic construction `DynamicParabolic`.

## Nonarchimedean local fields

Now `F` is a nonarchimedean local field, `M : IntegralModel 𝒪[F] F G`, `G` has
affine underlying scheme, and `χ` is a cocharacter of `M.group`. The generic
cocharacter `M.genericCocharacter χ` is the published base change of `χ` to `F`
followed by `M.genericIso.hom`.

`range_centralizerHom_genericCocharacter` states that the Library centralizer
inclusion of the generic cocharacter, followed by `M.genericIso.inv`, has range the
dynamic centralizer of the base-changed cocharacter of `χ`. This is the presentation
hypothesis of the previous section, for `p` the centralizer inclusion of
`M.genericCocharacter χ`. Its proof transports the representation along the
generic identification (`Dynamic.centralizer_eq_comap_of_iso`).

`leviMaximal_of_isTorus_specialCentralizer` assumes:

- `G` is connected reductive, and the special fibre of `M.group` over `𝓀[F]` is
  connected reductive;
- the special fibre over `𝓀[F]` of the integral centralizer scheme
  `Dynamic.Affine.centralizerScheme χ` is a torus (`IsTorus`);
- `M.integralPoints` is open in `G(F)` for the rational-point topology
  `rationalPointTopology F G.X`.

It concludes that every compact subgroup `C` of `G(F)` contained in the rational
points of the dynamic centralizer of `M.genericCocharacter χ` satisfies
`C ≤ M.integralPoints`. It does not use the extra hypothesis
`M.integralPoints ⊓ Z(F) ≤ C` of the published `LeviMaximalCocharacterStatement`.

Proof. For `g ∈ C`, the rational-point topology makes `G(F)` a topological group
(`rationalPoint_isTopologicalGroup`), so `g ^ n ∈ M.integralPoints` for some
`n > 0` (`exists_pow_mem_of_isCompact_of_isOpen`). Since the centralizer inclusion
represents the centralizer, `g` is the image of a rational point `ℓ` of the
generic centralizer `L`. Let `Z` be the centralizer model above with its inclusion
`φ`. The image of `ℓ ^ n` is `g ^ n`, so `ℓ ^ n ∈ Z.integralPoints` by
`Hom.mem_integralPoints_of_map_mem`. The generic group `L` is connected reductive
by the published `dynamicCentralizerReductive`, and the special fibre of `Z.group`
is a torus by hypothesis, so `mem_integralPoints_of_pow_mem_of_isTorus_special`
gives `ℓ ∈ Z.integralPoints`. Finally `Hom.map_mem_integralPoints` gives
`g ∈ M.integralPoints`. The smoothness of `M.group` used to build `Z` comes from
`isSmooth_of_reductive_localField`.

## Provenance

These are internal constructions for the published target
`LeviMaximalCocharacterStatement`. They implement the Levi step of Maculan (2017),
proof of Lemma 5.1, Claim (printed p. 14 / PDF p. 15): the intersection of a bounded
group with the rational points of the generic fibre `T` of a maximal `𝒪`-torus
lies in `T(𝒪)`, by Proposition 4.6. Here the torus is the integral dynamic
centralizer of a cocharacter, boundedness is replaced by compactness together with
openness of the integral points, and Proposition 4.6 is replaced by its power form
`mem_integralPoints_of_pow_mem_of_isTorus_special`. The Lean statements are not
quoted from that source.
