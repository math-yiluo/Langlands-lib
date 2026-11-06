# Universal homomorphism families tested on affine schemes

Module `Langlands.GroupScheme.HomScheme.AffineTest`, namespace `Langlands.GroupScheme.HomScheme`.

Let `H` and `G` be group schemes over a scheme `S`. A family `i : RelativeHom H G M` over
`M : Over S` is universal (`IsUniversal i`, from `HomScheme.Universal`) when, for every test
scheme `T : Over S`, evaluation `a ↦ evaluate a i` is a bijection from the maps `T ⟶ M` to
`RelativeHom H G T`. This file gives two tools for proving universality. First, it suffices to
test affine `T`. Second, universality is preserved by isomorphisms of the source and target group
schemes.

This is internal infrastructure for the task "Prove smooth moduli of actual closed torus
subgroups" (SGA 3, Exp. XI, 4.1, torus case), where it is used to show that `Hom(μ_m^I, G)` is
represented. No literature statement is formalized here. The lemmas are standard facts about
Zariski sheaves: morphisms of schemes and morphisms out of base changes glue along open covers.

## Base change along open immersions (`section OpenImmersion`)

For `a : W ⟶ T` in `Over S`:

- `isPullback_baseChangeProj H a`: the canonical projection `baseChangeProj H a : H_W ⟶ H_T` is
  the base change of `a.left` along the projection `H_T ⟶ T`.
- The instance: if `a.left` is an open immersion, so is `baseChangeProj H a`.
- `range_baseChangeProj H a`: the image of `baseChangeProj H a` is the preimage of the image of
  `a.left` under `H_T ⟶ T`.

## Locality and affine tests

- `relativeHom_eq_of_locally i j`: let `i j : RelativeHom H G T`. Suppose that every point of `T`
  lies in the image of some open immersion `a : W ⟶ T` with `evaluate a i = evaluate a j`. Then
  `i = j`. The proof uses `relativeHom_ext`, so it suffices to compare the projections to
  `G`. These agree on the open subschemes `H_W` of `H_T`, by `evaluate_fst`, and the opens cover
  `H_T` by `range_baseChangeProj`.
- `affineCoverOver T k` and `affineCoverHom T k` are the `k`-th member of the chosen affine open
  cover `T.left.affineCover`, as an object of `Over S`, and its inclusion into `T`. The instances
  say that it is affine and that the inclusion is an open immersion.
- `bijective_evaluate_of_iso i e h`: let `e : T ≅ T'`. If evaluation of `i` is bijective on maps
  `T' ⟶ M`, it is bijective on maps `T ⟶ M`. Evaluation along `e.hom` and `e.inv` gives
  mutually inverse bijections, by `evaluate_comp` and `evaluate_id`.
- `isUniversal_of_affine i h`: if evaluation of `i` is bijective on maps `T ⟶ M` for every `T`
  with affine `T.left`, then `i` is universal.
  - Injectivity: two maps `T ⟶ M` with the same evaluation agree on every affine chart `T_k`, by
    injectivity there. By `Scheme.Cover.hom_ext`, they are then equal.
  - Surjectivity: let `χ : RelativeHom H G T`. Choose `g_k : T_k ⟶ M` evaluating to the
    restriction of `χ` to `T_k`. On every affine open of each overlap `T_k ×_T T_l`, the two
    restrictions evaluate to the same family. By injectivity there they agree, so the `g_k` agree
    on the overlaps. Then `Scheme.Cover.glueMorphisms` gives `g : T ⟶ M`, and
    `relativeHom_eq_of_locally` shows that `g` evaluates to `χ`.
  No gluing of group homomorphisms is needed: only morphisms into `M` are glued.

## Transport along isomorphisms (`section Transport`)

Let `eH : H' ≅ H` and `eG : G ≅ G'` be isomorphisms of group schemes over `S`.

- `transport eH eG i : RelativeHom H' G' T` is the composite
  `(eH.hom)_T ≫ i ≫ (eG.hom)_T`, with base change taken by the functor `baseChange T.hom`.
- `baseChange_map_left_fst` and `baseChange_map_left_snd` compute the two projections of a
  base-changed group homomorphism. `baseChangeProj_baseChange_map` says that `baseChangeProj`
  commutes with base-changed homomorphisms.
- `evaluate_transport`: evaluation commutes with transport. The proof compares the projections to
  `G'` with `relativeHom_ext`.
- `transportEquiv eH eG T : RelativeHom H G T ≃ RelativeHom H' G' T` has inverse
  `transport eH.symm eG.symm`.
- `IsUniversal.transport hi eH eG`: if `i` is universal, so is `transport eH eG i`. Its evaluation
  map is `transportEquiv` composed with the evaluation map of `i`.
