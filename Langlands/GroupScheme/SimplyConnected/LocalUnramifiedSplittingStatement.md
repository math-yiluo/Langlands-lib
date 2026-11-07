# Splitting of simply connected cocycles by finite unramified extensions

Authors: Worker 303.

`Langlands.GroupScheme.LocalSimplyConnectedUnramifiedSplittingStatement.{u}` is a
proposition definition at arbitrary universe `u`. This module states it and
proves nothing.

## Exact statement

Let `F : Type u` have the instances `[Field F] [ValuativeRel F]
[TopologicalSpace F] [IsNonarchimedeanLocalField F]`. Let `G` be an actual group
scheme over `Spec F` with `[IsAffineHom G.X.hom]` and `IsSimplyConnected G`. The
imported predicate `IsSimplyConnected` includes `IsSemisimple G` and algebraic
simple connectedness; it is not a topological condition.

Take any field `M : Type u` with `[Algebra F M] [FiniteDimensional F M]
[IsGalois F M]` and any actual `ξ : Cocycle G U`, where

```
U = Over.mk (Spec.map (CommRingCat.ofHom (algebraMap F M))).
```

The conclusion is that there exist

- `E : IntermediateField F (SeparableClosure F)` with `FiniteDimensional F E`
  and `E ≤ LocalGalois.Separable.inertiaFixedField F`, and with
  `W = Over.mk (Spec.map (CommRingCat.ofHom (algebraMap F E)))`;
- a morphism `g : U ⊗ W ⟶ G.X` over `Spec F`, where `U ⊗ W` is the cartesian
  product in `Over (Spec F)`, that is, the fibre product
  `Spec M ×_{Spec F} Spec E`;

such that for every test scheme `Z` over `Spec F` and all `a b : Z ⟶ U ⊗ W`
with `a ≫ snd U W = b ≫ snd U W`,

```
ξ.toFun (a ≫ fst U W) (b ≫ fst U W) = (a ≫ g) * (b ≫ g)⁻¹.
```

`Cocycle` is that of `Langlands.GroupScheme.TorsorCocycle`. The imported
`inertiaFixedField F` is the fixed field in `SeparableClosure F` of the inertia
subgroup, that is, the maximal unramified extension `F^ur` of `F` in that
separable closure. So `E` is a finite unramified extension of `F`. The
published theorem `Langlands.LocalGalois.Separable.separableUnramified` shows
that, for finite `E`, this containment is equivalent to arithmetic
unramifiedness. No embedding of `M` into the separable closure is required.

The displayed identity says that the base change of `ξ` to `E` is a coboundary.
`U ⊗ W ⟶ W` is the cover `Spec (M ⊗_F E) → Spec E`, and two points of
`U ⊗ W` with the same image in `W` form a point of its Čech square over `W`.
On such pairs the base-changed cocycle has the value
`ξ.toFun (a ≫ fst U W) (b ≫ fst U W)`, and `g` is a cochain on this cover whose
coboundary is that value. The statement makes no restriction on the
characteristic of `F` and no isotropy, almost-simplicity, splitness or
quasi-splitness assumption on `G`.

## Source and derived formulation

Provenance: derived.

T. Kaletha and G. Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
registered as `kaletha-prasad-2023-bruhat-tits-new-approach`,
Proposition 2.3.5 (printed p. 81 / PDF p. 112): for a discretely valued
Henselian field `K` with algebraically closed residue field (the setting of
§2.3, printed p. 80 / PDF p. 111) and a connected reductive `K`-group `G`, one
has `H¹(K, G) = {1}`. The maximal unramified extension `F^ur` of a
nonarchimedean local field `F` is such a field, and a semisimple `F`-group is
connected reductive. KP Theorem 10.6.1 (printed p. 397 / PDF p. 428) uses this
proposition in the same way, to identify `H¹(Gal(F^ur/F), G(F^ur))` with
`H¹(F, G)`.

The present proposition is the finite-level Čech consequence. The cocycle `ξ`
is a descent datum on the trivial torsor over `Spec M`, so it defines a
`G`-torsor `P` over `F`, with a point over `M` whose coboundary is `ξ`. Since
`G` is smooth, `P` is classified by Galois cohomology, so it becomes trivial
over `F^ur`. Since `P` is of finite type and `F^ur` is the union of its finite
subextensions, `P` has a point over some finite `E ⊆ F^ur`. Comparing this
point with the point over `M` on `Spec (M ⊗_F E)` gives `g`. This paragraph
explains where the formulation comes from. The module proves none of these
steps, and it defines no torsor or Galois cohomology object.

## Purpose

This is one of the two inputs of
`Langlands.GroupScheme.localSimplyConnectedGaloisCocycleVanishing_of_unramified`
in `Langlands.GroupScheme.SimplyConnected.LocalGaloisCocycleVanishingUnramifiedReduction`.
The other input,
`Langlands.GroupScheme.LocalSimplyConnectedUnramifiedCocycleVanishingStatement`,
says that every cocycle on a finite unramified cover is trivial. Together they
give `Langlands.GroupScheme.LocalSimplyConnectedGaloisCocycleVanishingStatement`.
The derivation above uses only that `G` is connected reductive. The
simple-connectedness hypothesis is kept so that the binders match those of the
Galois-cover statement.
