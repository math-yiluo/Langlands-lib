# Proof that Galois twisting preserves norm-one adelic points (Lemma C)

This module proves `twistPoint_mem_normOneSubgroup : TwistPointNormOneStatement`, stated in
`AdelicGaloisTwistNormOne`. It is an input of the proof of `GaloisBorelTwistingStatement`
(clause 4 of `IsGaloisBorelTwist`, norm-one points of the minimal standard parabolic).

Setting: `L/F` is a finite Galois extension of number fields, `σ ∈ Gal(L/F)`, `H` is a group
scheme over `Spec L`, `H^σ` is its base change along `Spec σ`, and `twistPoint F L σ H p` is
the `𝔸_L`-point of `H^σ` that corresponds, under the pullback adjunction, to `p` precomposed
with `Spec σ̃`. Here `σ̃` is the automorphism `σ ⊗ 1` of `𝔸_L = L ⊗_F 𝔸_F`.

## Declarations

- `isIso_mapPullbackAdj_counit` (instance): for an isomorphism of schemes `a`, the counit
  `pullback.fst` of the adjunction `Over.map a ⊣ Over.pullback a` is an isomorphism. Each
  component is `pullback.fst Z.hom a`, which is an isomorphism because `a` is, and
  `Over.forget` reflects isomorphisms.
- `baseChangeFullyFaithful a`: base change of group schemes along an isomorphism of schemes
  is fully faithful. This is `Adjunction.fullyFaithfulROfIsIsoCounit` followed by
  `Functor.FullyFaithful.mapGrp`.
- `exists_baseChange_character`: every character `ψ : H^a ⟶ 𝔾_m` is
  `(baseChange a).map χ ≫ Gm.baseChangeIso a` for some character `χ : H ⟶ 𝔾_m`. Take `χ` to be
  the preimage of `ψ ≫ (Gm.baseChangeIso a).inv`.
- `isIso_galoisBaseMap`: `Spec σ` is an isomorphism, as `Spec` of a ring isomorphism.
- `characterUnits_val`: the value of `characterUnits` is the image under `ΓSpecIso` of the
  global unit given by `Gm.pointsEquiv` of the composite point. This holds by definition.
- `character_twistPoint`: if `ψ = (baseChange (Spec σ)).map χ ≫ Gm.baseChangeIso`, then
  `ψ(twistPoint p) = σ̃(χ(p))` in the ideles of `L`.
- `twistPoint_mem_normOneSubgroup`: the main result.

## Proof

Let `ψ` be a character of `H^σ` and take `χ` as in `exists_baseChange_character`. The unit
`ψ(twistPoint p)` is computed in the following steps:

1. `Gm.pointsEquiv_baseChangeIso_hom` removes `Gm.baseChangeIso`.
2. `Gm.baseChangeUnitsEquiv_apply` rewrites the unit through the pullback adjunction.
3. `baseChangePointsEquiv_comp` moves `(baseChange a).map χ` through the adjunction.
4. `baseChangePointsEquiv_twistPoint` turns the point into `(adeleTestIso σ).hom ≫ p`.
5. `Gm.pointsEquiv_naturality` shows that precomposing with `(adeleTestIso σ).hom`, whose
   underlying scheme map is `Spec σ̃`, applies `(Spec σ̃).appTop` to the global unit.

After `ΓSpecIso`, `Scheme.ΓSpecIso_naturality` identifies this map with `σ̃`. Hence
`ψ(twistPoint p) = AdeleGalois.idelesMap σ (χ(p))`. The theorem `AdeleGalois.full_idelesMap`
says that `σ̃` preserves the normalized idelic norm, so `|ψ(twistPoint p)| = |χ(p)| = 1`, the
last equality because `p` has norm one.

## Provenance

This is internal infrastructure for the Library's Galois-descent route to Springer's
fundamental-set theorem (Springer 1994, §3.6). The underlying fact is standard: Galois
conjugation of adelic points commutes with taking absolute values of characters, because
`|σ̃(x)| = |x|` on the ideles. The proof follows the route Worker 5268 proposed in
`AdelicGaloisTwistNormOne.md`.
