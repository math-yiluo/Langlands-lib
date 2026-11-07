# Local vanishing for simply connected cocycles on finite unramified covers

Authors: Worker 303.

`Langlands.GroupScheme.LocalSimplyConnectedUnramifiedCocycleVanishingStatement.{u}`
is a proposition definition at arbitrary universe `u`. This module states it and
proves nothing.

## Exact statement

Let `F : Type u` have the instances `[Field F] [ValuativeRel F]
[TopologicalSpace F] [IsNonarchimedeanLocalField F]`. Let `G` be an actual group
scheme over `Spec F` with `[IsAffineHom G.X.hom]` and `IsSimplyConnected G`. The
imported predicate `IsSimplyConnected` includes `IsSemisimple G` and algebraic
simple connectedness; it is not a topological condition.

Take any `E : IntermediateField F (SeparableClosure F)` with
`[FiniteDimensional F E]` and `E ≤ LocalGalois.Separable.inertiaFixedField F`,
and set

```
W = Over.mk (Spec.map (CommRingCat.ofHom (algebraMap F E))).
```

The conclusion is that every actual `ξ : Cocycle G W` satisfies `ξ.IsTrivial`:
some `f : W ⟶ G.X` satisfies `ξ.toFun a b = (a ≫ f) * (b ≫ f)⁻¹` for every test
scheme `Z` over `Spec F` and all `a b : Z ⟶ W`. `Cocycle` and `IsTrivial` are
those of `Langlands.GroupScheme.TorsorCocycle`.

The imported `inertiaFixedField F` is the fixed field in `SeparableClosure F` of
the inertia subgroup of `Gal(SeparableClosure F/F)`, that is, the maximal
unramified extension `F^ur` of `F` in that separable closure. So the hypothesis
on `E` says that `E` is a finite unramified extension of `F` inside `F^ur`. The
published theorem `Langlands.LocalGalois.Separable.separableUnramified` shows
that, for finite `E`, this containment is equivalent to arithmetic
unramifiedness of the spectral integer and residue extension. No `IsGalois`
hypothesis is imposed. The statement makes no restriction on the
characteristic of `F` and no isotropy, almost-simplicity, splitness or
quasi-splitness assumption on `G`.

## Source and derived formulation

Provenance: derived.

T. Kaletha and G. Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
registered as `kaletha-prasad-2023-bruhat-tits-new-approach`. Chapter 10
(printed p. 389 / PDF p. 420) assumes that `k` is discretely valued with
Henselian valuation ring and perfect residue field of dimension at most one,
lets `K` be a maximal unramified extension of `k`, and sets `Γ = Gal(K/k)`. A
nonarchimedean local field satisfies these assumptions, since its residue field
is finite.

- Theorem 10.6.1 (printed p. 397 / PDF p. 428) shows, for connected reductive
  `G` and a `Γ`-stable Iwahori subgroup `I` of `G(K)` with normalizer `N`, that
  the maps `H¹(Γ, N/I) ← H¹(Γ, N) → H¹(Γ, G(K)) → H¹(k, G)` are bijective.
- Theorem 10.6.4 (printed p. 399 / PDF p. 430) states that `H¹(k, G)` is
  trivial for simply connected semisimple `G`. Its proof shows that `I` is its
  own normalizer, so `N/I` is trivial, and applies Theorem 10.6.1.

Together these give `H¹(Γ, G(K)) = 1`, the unramified part of the vanishing.
The present proposition is its finite-level Čech form. For a local field `k`,
`Γ` is identified with the Galois group of the residue extension, the
profinite completion of `ℤ`. It is abelian, so every finite subextension `E`
of `K/k` is Galois over `k`. Inflation
`H¹(Gal(E/k), G(E)) → H¹(Γ, G(K))` is injective. On the Čech side,
`E ⊗_k E` is the product of copies of `E` indexed by `Gal(E/k)`, so a cocycle on
`Spec E → Spec k` is a crossed homomorphism `Gal(E/k) → G(E)`, and triviality
is the Galois coboundary identity. The Library theorem
`Langlands.GroupScheme.GaloisCocycle.isTrivial_iff` records this comparison for
its `GaloisCocycle.cover` presentation of the spectrum of a finite Galois
extension. This paragraph explains where the formulation comes from. The
module proves neither the inflation argument nor any comparison, and it
defines no Galois cohomology object.

The proposition is also a special case of the vanishing of `H¹(k, G)` itself,
since `Spec E → Spec F` is a finite separable cover. It is stated separately
because the Bruhat–Tits argument of Theorem 10.6.1 proves exactly this
unramified part, without Steinberg's theorem over `K`.

## Purpose

This is one of the two inputs of
`Langlands.GroupScheme.localSimplyConnectedGaloisCocycleVanishing_of_unramified`
in `Langlands.GroupScheme.SimplyConnected.LocalGaloisCocycleVanishingUnramifiedReduction`.
The other input,
`Langlands.GroupScheme.LocalSimplyConnectedUnramifiedSplittingStatement`, says
that every cocycle on a finite Galois cover splits over a finite unramified
extension. Together they give
`Langlands.GroupScheme.LocalSimplyConnectedGaloisCocycleVanishingStatement`.
