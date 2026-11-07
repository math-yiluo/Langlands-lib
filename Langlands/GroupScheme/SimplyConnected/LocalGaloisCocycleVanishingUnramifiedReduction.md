# From finite unramified covers to finite Galois covers

Authors: Worker 303.

## Result

`Langlands.GroupScheme.localSimplyConnectedGaloisCocycleVanishing_of_unramified`
proves, at arbitrary universe `u`,

```
LocalSimplyConnectedUnramifiedSplittingStatement.{u} →
  LocalSimplyConnectedUnramifiedCocycleVanishingStatement.{u} →
    LocalSimplyConnectedGaloisCocycleVanishingStatement.{u}
```

The first hypothesis says that every cocycle of a semisimple simply connected
group over a nonarchimedean local field `F`, on a finite Galois cover
`Spec M`, becomes a coboundary over some finite unramified extension `E`. The
second says that every cocycle on a finite unramified cover `Spec E` is
trivial. The conclusion is that every cocycle on a finite Galois cover is
trivial. The theorem proves neither hypothesis.

## Proof

Fix `F`, `G` and a cocycle `ξ` on `U = Spec M`. The splitting hypothesis gives
a finite `E ≤ inertiaFixedField F` with cover `W = Spec E`, and a morphism
`g : U ⊗ W ⟶ G.X` whose coboundary equals `ξ (a ≫ fst, b ≫ fst)` on pairs
`a b : Z ⟶ U ⊗ W` with `a ≫ snd = b ≫ snd`.

1. `fieldExtension_fpqc` from `Langlands.GroupScheme.BaseChangeReflection`
   shows that `U.hom` and `W.hom` are surjective, flat and quasi-compact. The
   two projections `fst U W` and `snd U W` are pullbacks of these maps, so they
   are surjective, flat and quasi-compact too.
2. Let `ζ` be the refinement of `ξ` along `fst U W`, twisted by `g`
   (`Cocycle.refine`, `Cocycle.twist`). Its value is
   `(a ≫ g)⁻¹ * ξ (a ≫ fst, b ≫ fst) * (b ≫ g)`. By the splitting identity this
   is `1` whenever `a ≫ snd = b ≫ snd`.
3. `Cocycle.isTrivial_of_comp_eq` from `Langlands.GroupScheme.CocycleDescent`,
   applied to `ζ` and `snd U W`, shows that `ζ` is trivial. Its other input,
   that every cocycle on `W` is trivial, is the unramified vanishing
   hypothesis applied to `E`.
4. `Cocycle.IsTrivial.of_twist` shows that the refinement of `ξ` along
   `fst U W` is trivial. `Cocycle.isTrivial_refine_iff` from
   `Langlands.GroupScheme.CocycleRefinement`, for the fpqc map `fst U W`,
   reflects triviality to `ξ`.

## Provenance

Internal. The argument is the standard inflation–restriction reasoning for
`H¹(Gal(F^ur/F), G(F^ur)) → H¹(F, G)` used in the proof of KP Theorem 10.6.1
(Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach*, printed p. 397 /
PDF p. 428). A class whose restriction to `F^ur` is trivial is inflated from
`Gal(F^ur/F)`, and such an unramified class is trivial. Here it is carried out
for Čech cocycles on finite covers, with an explicit twist in place of the
inflation–restriction sequence. Combined with
`localSimplyConnectedCocycleVanishing_of_galois` in
`Langlands.GroupScheme.SimplyConnected.LocalCocycleVanishingGaloisReduction`,
this theorem reduces
`Langlands.GroupScheme.LocalSimplyConnectedCocycleVanishingStatement` to the two
hypotheses.
