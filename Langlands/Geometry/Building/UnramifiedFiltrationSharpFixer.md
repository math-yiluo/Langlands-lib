# Descended root filtrations lie in the sharp fixer over the extension

This module proves one inclusion of subgroups, used in the unramified descent of
the building. Work over an arbitrary field extension `K/k` in universe `u`, with an
affine smooth `k`-group `G`. Let `iS : S.toGrp ⟶ G` be a monomorphic torus
embedding with `S` split over `k`, and let `f : S ⟶ T` be a morphism to a second
commutative `k`-group scheme with `iT : T.toGrp ⟶ G` and
`CommGroupScheme.groupHom f ≫ iT = iS`. Over `K`, the scalar extension
`iT_K : T_K ⟶ G_K` is assumed monomorphic, `T_K` split, and `iT_K` to have
opposite factor pairs (`RelativeRoot.HasOppositeFactorPairs`). Neither torus is
assumed maximal, and `x` is not assumed to be fixed by any Galois action.

## Statements

- `baseChange_groupHom_comp_of_factorization f hf` states that the factorization
  survives scalar extension:
  `groupHom f_K ≫ iT_K = iS_K`, where `f_K`, `iT_K` and `iS_K` are the images of `f`,
  `iT` and `iS` under the base-change functors along `algebraBaseMap k K`.
  It needs no hypothesis on `G` or the tori.

- `filtration_le_comap_sharpFixer_of_torusFieldRestriction f hf hS hT hE D x DS w hw a`
  takes:
  - `D`, any apartment class (`KPApartmentData`) for `(G_K, T_K)`, for any `ω : Kˣ → ℝ`;
  - a point `x` of its apartment;
  - `DS`, any apartment class for `(G, S)`, for any `ω' : kˣ → ℝ`;
  - a point `w` of the apartment of `DS` whose valuation equals
    `torusFieldRestrictedRootFunctionFamily hS hT hE (D.isRootDatumValuation_of_mem x.mem) f_K`
    (hypothesis `hw`). This is the torus-then-field restriction of the valuation `x`,
    the same map `φ` that appears in `UnramifiedValuationDescentStatement`.

  It concludes that for every root `a` of `(G, S)` the depth-zero filtration group
  `DS.filtration w a 0` lies in the preimage of the sharp fixer `D.sharpFixer {x}`
  (KP's `G(K)^♯_x`, Definition 7.4.1) under `rationalExtend k K G : G(k) → G(K)`.

For `K` the maximal unramified extension of a nonarchimedean local field, this is
the inclusion `U_{a,x,0} ⊆ G(K)^♯_x ∩ G(k)` behind Kaletha–Prasad (2023),
Lemma 9.6.3 (printed p. 366, PDF p. 397). That lemma states
`U_{a,x,r} = U_a(k) ∩ ∏_b U_{b,x,r}`, where the product runs over the non-divisible
roots `b` of `(G_K, T_K)` that restrict to `a` or `2a`. Each `U_{b,x,0}` lies in
`G(K)^♯_x` by definition. The Lean statement is only this inclusion at depth `0`,
and only for the restricted valuation of the Library. It does not prove
Lemma 9.6.3 itself.

## Proof

The factorization lemma rewrites `iS` as `groupHom f ≫ iT`, applies
`Functor.map_comp` and closes by definitional unfolding (`groupHom` commutes with base
change by `rfl`). The same argument appears inside the published
`RelativeRootGroupAbsoluteGenerationProof`.

For the main theorem, `g ∈ DS.filtration w a 0` is by definition
`g ∈ rootFiltration iS w.val a 0`. After rewriting `w.val` with `hw`, the published
`rootFiltration_torusFieldRestrictedRootFunctionFamily` (module
`RootValueTorusFieldRestriction`, with the base-changed factorization above as
`hfactor`) identifies this set with `torusFieldRestrictedRootDepthSubgroup`. That is
the preimage under `rationalExtend k K G` of `torusRestrictedRootDepthSubgroup hφ f_K a_K 0`,
with `a_K` the base change of `a`. That subgroup is defined as a supremum, over the
roots `χ` of `iT_K` and positive integers `m` with `f_K ≫ χ = m • a_K`, of
`hφ.filtrationSubgroup χ (m * 0)`. So it suffices to bound each term. After
`mul_zero`, each term is definitionally `D.filtration x χ 0`. By `rootFixer_singleton`
this equals `D.rootFixer χ {x}`, and `rootFixer_le_sharpFixer` puts it inside
`D.sharpFixer {x}`.

## Provenance

The statements are internal helper lemmas for the reduction of
`UnramifiedBuildingDescentStatement`. The proof composes published Library results:
`rootFiltration_torusFieldRestrictedRootFunctionFamily`,
`torusRestrictedRootDepthSubgroup`, `KPApartmentData.rootFixer_singleton` and
`KPApartmentData.rootFixer_le_sharpFixer`. No new definition is introduced. The
module has a private `IsAffineHom` instance for `G_K`, the same pullback argument as
in `RootValueTorusFieldRestriction`.
