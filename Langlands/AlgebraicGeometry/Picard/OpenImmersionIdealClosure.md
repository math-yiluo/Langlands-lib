# Actual module-sheaf closure along an open immersion

This module supplies the categorical construction used in the invertible-ideal extension proof. It constructs actual sheaves, morphisms, and an isomorphism. It does not assert that the constructed module is locally free or quasicoherent.

Let `j : Y ⟶ X` be an open immersion and let `s : D ⟶ O_Y` be any morphism of module sheaves. Here `O_X` and `O_Y` mean `SheafOfModules.unit` for the respective ring sheaves.

## Construction

In namespace `Langlands.AlgebraicGeometry.Picard.OpenImmersionIdeal`, `closure j s` is the categorical pullback

```
closure j s  --inclusion--> O_X
     |                       |
 projection          unitToPushforwardUnit j
     |                       |
     v                       v
    j_*D --------j_*s-----> j_*O_Y.
```

The two projections are `inclusion j s` and `projection j s`, and `condition` is the pullback's commuting equation. If `s` is monic, its pushforward is monic because pushforward is a right adjoint; the pullback projection `inclusion j s` is therefore monic. The construction is the inverse image of the pushed-forward submodule inside the actual structure module. It also makes sense without assuming `s` monic.

## Restriction comparison

`restrictionIso j s` is an actual isomorphism

```
(Scheme.Modules.pullback j).obj (closure j s) ≅ D.
```

Its hom is the pullback of `projection j s` followed by the counit of the pullback-pushforward adjunction. `restrictionIso_hom_inclusion` proves the precise equation

```
(Scheme.Modules.pullback j).map (inclusion j s) ≫
    (Langlands.Scheme.Modules.pullbackUnitIso j).hom =
  (restrictionIso j s).hom ≫ s.
```

The proof first uses the published `OpenCohomologyVanishing.preservesFiniteLimits_pushforward` to obtain finite-limit preservation for the concrete restriction functor. It transports preservation to pullback through `Scheme.Modules.restrictFunctorIsoPullback`. The published `pullbackUnitAdjunction` identifies the pullback of `unitToPushforwardUnit`, followed by the counit, with `pullbackUnitIso.hom`. The counit is invertible because pushforward along an open immersion is fully faithful. Consequently the pullback of `unitToPushforwardUnit` is invertible, and the second projection of the mapped pullback square is invertible. This gives `restrictionIso`. Mapping `condition` and applying counit naturality proves the inclusion equation.

`map_unitToPushforwardUnit_counit` itself holds for every scheme morphism; the remaining comparison construction uses the open immersion hypothesis. No local Noetherianity, factoriality, integrality, reducedness, separation, or quasi-compactness is assumed here.

## Provenance and scope

This is an internal categorical construction derived from Mathlib's pullbacks, the module-sheaf restriction and pullback adjunctions, and the Library's canonical pullback-unit comparison. It provides the actual maps for the ideal-extension target. Establishing local rank one under factoriality on the complement is separate mathematical work; none of those hypotheses or conclusions are encoded in this construction.
