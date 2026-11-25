# Inverse parabolic construction in a central product over a field

This is an internal support construction for the derived group correspondence. It combines the field dynamic parabolic characterization with reflection through a closed subgroup and restriction of a supplied central product isogeny. It does not prove the arbitrary base correspondence.

## Transport from the actual intersection

`exists_centralIsogeny_of_intersection_range_eq` works over any scheme `S`. Suppose `z : Z → G` is central, `d : D → G` is any homomorphism, and their commuting multiplication `Z × D → G` is a central isogeny. Let `i : P → G` be monic on the underlying schemes over `S`, and suppose the all-test range of `z` is contained in the range of `i`. If `i' : P' → D` is another monic subgroup presentation with the same all-test range as the first projection `D ×_G P → D`, then there is a central isogeny `e : Z × P' → P` satisfying exactly

`e ≫ i = prodHom z (i' ≫ d) (hz.commute_values _)`.

The proof identifies `P'` with the actual intersection by uniqueness of represented subgroup functors. Tensoring this isomorphism with `Z` and precomposing the restricted central product gives `e`. The imported `isCentralIsogeny_centralProductIntersectionFactor` supplies centrality of the full scheme-theoretic kernel and the finite, flat, surjective, locally finitely presented morphism conditions. The proof transports those properties using `IsCentralIsogeny.iso_comp`. A private product naturality lemma proves the exact multiplication equation. This argument requires no reductivity, torus or field assumptions and does not identify an isogeny's pointwise image with its target.

## A chosen field cocharacter

Let `k` be any field, `D` a connected reductive group over `k`, and `i' : P' → D` a parabolic subgroup. `CentralProductParabolic.extensionCocharacter hD i' hi'` chooses a cocharacter `χ : Gm_k → D` from `ParabolicDynamicProof.exists_dynamicPresentation_of_isParabolicSubgroup`. Its specification `range_extensionCocharacter` says

`SubgroupFunctor.range i' = Dynamic.parabolic χ`.

This is a classical choice of presentation, with no uniqueness assertion.

## Inverse parabolic construction

`CentralProductParabolic.exists_inverse` assumes connected reductive field groups `G` and `D`, a closed embedding `d : D → G`, a central homomorphism `z : Z → G`, and a central isogeny `prodHom z d`. For every parabolic `i' : P' → D`, it constructs a group scheme `P`, a parabolic embedding `i : P → G`, and a central isogeny `e : Z × P' → P`. They satisfy both the exact multiplication equation above and

`SubgroupFunctor.range (subgroupIntersectionFst d i) = SubgroupFunctor.range i'`.

The implemented proof takes `P` to be the affine representative of the dynamic parabolic `P_G(χ ≫ d)`, with its constructed closed inclusion. Field parabolic recognition proves that inclusion is parabolic. Centrality places the entire all-test range of `z` in the dynamic centralizer and hence in this parabolic. Closed subgroup reflection identifies the preimage of `P_G(χ ≫ d)` in `D` with `P_D(χ)`, so the actual intersection has precisely the range of `i'`. The general transport theorem then supplies `e` and its multiplication identity.

There is no perfectness or characteristic restriction on `k`. The group `Z` need not be a torus for this support result. No normality or semisimplicity premise is needed beyond the stated connected reductivity and supplied central product isogeny. Relative smoothness and descent over arbitrary base schemes, and the existence of the global central product isogeny, remain outside this module.

## Provenance and supporting files

The construction is derived internally from the named dynamic parabolic and represented subgroup interfaces, the scheme-theoretic intersection range identity, and isomorphism invariance of central isogenies. The `CentralIsogeny/Pullback` and `CentralIsogeny/ProductIntersectionRestriction` pairs, ported together with this module, are reused byte-identically from earlier work. Their proofs give the Cartesian restriction of a central product, including full kernel centrality. The field construction and transport argument are new in this module. This focused support module does not assert the arbitrary base derived group correspondence without its remaining geometric inputs.
