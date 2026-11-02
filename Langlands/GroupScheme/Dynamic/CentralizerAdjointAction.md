# Conjugation action of a represented dynamic centralizer on the unipotent subgroup

Let `G` be a group scheme over any scheme `S`, let `χ : G_m → G` be an actual
cocharacter, and suppose the published dynamic subgroup functors `Z(χ)`
(`Dynamic.centralizer χ`) and `U(χ)` (`Dynamic.unipotent χ`) are represented by
homomorphisms `iZ : Z → G` and `iU : U → G`. When `P(χ)` is a parabolic
subgroup, `Z(χ)` is its Levi factor `M`. Everything is tested on all
`T : Over S`, including nonreduced test schemes.

All declarations lie in `Langlands.GroupScheme.Dynamic` and take the
representation hypotheses `hZ` and `hU` as explicit arguments.

## Declarations

- `range_unipotent_isNormalizedBy_range_centralizer hZ hU`: the subgroup
  functor `range iU` is normalized by `range iZ`.
- `centralizerAdjointAction hZ hU : AutomorphicAction Z U`: the action of `Z`
  on `U` by normalized conjugation.
- `centralizerAdjointAction_act_comp`: for all test points `m : T → Z` and
  `u : T → U`,
  `(centralizerAdjointAction hZ hU).act m u ≫ iU =
    iZ(m) * iU(u) * iZ(m)⁻¹`.
  So `m` acts by `u ↦ m u m⁻¹`: the left factor is `m`, the right factor
  is `m⁻¹`.
- `eq_centralizerAdjointAction`: any `b : AutomorphicAction Z U` that
  satisfies the same formula for all test points equals
  `centralizerAdjointAction hZ hU`.

The construction assumes no field, separatedness, smoothness, affineness or
finiteness. The two representation hypotheses are explicit. Nothing here
constructs a Lie algebra, a determinant or a character.

## Provenance and proof

This is an internal specialization of
`AutomorphicAction.ofNormalizedConjugation`, which bundles the published
`SubgroupFunctor.normalizedConjugation` and its action laws. It is the
analogue for `Z(χ)` of the published `Dynamic.parabolicConjugation` for
`P(χ)`. No structural claim from the literature is used.

`range_unipotent_isNormalizedBy_range_centralizer` rewrites both ranges by
the equalities in `hU` and `hZ`. A point of `Z(χ)(T)` lies in `P(χ)(T)` by
the published `Dynamic.centralizer_le_parabolic`. The published
`Dynamic.unipotent_isNormalizedBy_parabolic` then shows that conjugation
by it preserves `U(χ)(T)`.

`centralizerAdjointAction` applies `ofNormalizedConjugation` to `iU`, `iZ`
and this normalization result. The monomorphism instance it needs is the
first component of `hU`. `centralizerAdjointAction_act_comp` is the
published point formula
`SubgroupFunctor.lift_comp_normalizedConjugation_comp`.
`eq_centralizerAdjointAction` uses the published extensionality
`AutomorphicAction.ext_act`. At every pair of test points, both actions
give the same point after `iU` by the hypothesis and
`centralizerAdjointAction_act_comp`. Since `iU` is a monomorphism, the
points are equal.

## Role

The Levi subgroup acts on the Lie algebra of the unipotent radical through
this action, with the orientation `u ↦ m u m⁻¹`. That representation gives
the algebraic modulus character of a parabolic restricted to its Levi
subgroup. Renard, *Représentations des groupes réductifs p-adiques*
(version of 9 July 2026), §V.5.4, printed pp.126–127 / PDF pp.132–133,
writes the modulus of a parabolic as a product over roots on its Lie
algebra. It is registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra* (2003), §I.1, printed pp.238–241 / PDF pp.4–7, sets up the
same notation. It is registered as `waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
These sources give context only; the module proves none of their claims.
