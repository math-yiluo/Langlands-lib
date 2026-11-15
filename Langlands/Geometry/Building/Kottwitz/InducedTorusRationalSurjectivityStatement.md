# The rational Kottwitz map of an induced torus is surjective

`Langlands.Geometry.Building.Kottwitz.InducedTorusKottwitzRationalSurjectivityStatement`
states Kaletha–Prasad, *Bruhat–Tits theory: a new approach* (Cambridge, 2023),
§11.1, Corollary 11.1.9, printed p. 425, PDF p. 456:

> Corollary 11.1.9 If T is an induced torus then κ : T(k) → X∗(T)^Γ_I is
> surjective.
>
> Proof Lemma 11.1.8 reduces to the case T = Gm, which is obvious.

The map `κ` on `T(k)` is defined just before Corollary 11.1.6 (printed p. 423,
PDF p. 454): for a `k`-torus `T`, KP "define κ_T : T(k) → π₁(T)^{Gal(K/k)}_I
as the restriction of κ_{T_K}", where `π₁(T) = X_*(T)` and `κ_{T_K}` is the map
of Proposition 11.1.1 (printed p. 421, PDF p. 452). Lemma 11.1.8, used in the
source proof, is on printed pp. 423–425, PDF pp. 454–456. The chapter's
conventions (`Θ = Gal(k^s/k)`, `I = Gal(k^s/K)`, `Γ = Gal(K/k)`, with `K` the
maximal unramified extension inside `k^s`) are on printed p. 420, PDF p. 451.
Induced tori are defined in Definition 2.5.1, printed p. 86, PDF p. 117.

The authors' corrections and additions (version of 1 November 2024) change only
§11.7 within Chapter 11 (p. 43 of the corrections). Their §2.5 entries (p. 24)
concern the sign of `ω_T` and Remarks 2.5.11 and 2.5.15. They change neither
Corollary 11.1.9, nor Lemma 11.1.8, nor the definition of `κ_T` on `T(k)`, nor
Definition 2.5.1.

## Setting and scope

KP's Chapter 11 works over a field `k` with a discrete valuation, a Henselian
ring of integers and a perfect residue field. The Lean statement uses the
setting of the existing maps `torusKottwitz` and `torusKottwitzRational`
(module `Langlands.Geometry.Building.Kottwitz.TorusMap`):

* the base field is any nonarchimedean local field `F : Type u` with
  `[Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]`;
  this is the source's `k`;
* `E = SeparableClosure F` is the source's `k^s`;
* `K = UnramifiedClosure F` is the maximal unramified extension of `F` inside
  `F^sep`, the fixed field of inertia. It is not completed, as in KP.

A nonarchimedean local field is complete, so its ring of integers is Henselian,
and its residue field is finite, hence perfect. So this is a special case of
KP's setting, and Corollary 11.1.9 applies to it.

The torus `T` is any commutative group scheme
`T : CommGroupScheme (Spec (CommRingCat.of F))` with `hT : IsInducedTorus T`.
`IsInducedTorus` (module `Langlands.GroupScheme.Torus.Induced`) is the
Library's form of KP Definition 2.5.1. It asks for a finite Galois extension
of `F` splitting `T` over which the character lattice has a `ℤ`-basis permuted
by the Galois group. `IsInducedTorus.isTorus hT : IsTorus T.toGrp` supplies the
torus hypothesis that `torusKottwitzRational` takes. That hypothesis is a
proposition, so the map does not depend on which proof of it is used.

## The statement

For every such `F` and `T`,

```
Function.Surjective (torusKottwitzRational F T hT.isTorus)
```

where

```
torusKottwitzRational F T hT.isTorus :
  rationalPoints T.toGrp →* Multiplicative (TorusInvariantTarget F T).
```

**Source.** `rationalPoints T.toGrp` is the group of `F`-points of `T`, the
source's `T(k)`.

**Target.** `TorusInvariantTarget F T` is
`inertiaInvariants F K E (cocharacterLattice.galoisRepresentation F E T)`. Here:

* the lattice is the actual geometric cocharacter group
  `cocharacterLattice ((CommGroupScheme.baseChange (algebraBaseMap F E)).obj T)`,
  the group-scheme homomorphisms `𝔾_m → T_E` over `Spec E`. This is KP's
  `X_*(T) = Hom_{k^s}(𝔾_m, T)`. The group `E ≃ₐ[F] E`, that is `Θ`, acts on it
  by `cocharacterLattice.galoisRepresentation`;
* `inertiaCoinvariants` is the quotient by the integral span of all
  differences `ν - σ ν` with `σ` in `relativeInertia F K E`. That subgroup is
  the kernel of restriction `Aut_F(E) → Aut_F(K)`, i.e. KP's `I = Gal(k^s/K)`.
  The quotient is KP's `X_*(T)_I`;
* `inertiaInvariants` is the submodule of `X_*(T)_I` fixed by the induced
  action `torusGammaRepresentation` of `K ≃ₐ[F] K`, KP's `Γ = Gal(K/k)`. It is
  KP's `X_*(T)_I^Γ`.

The group law on the target is the addition of `X_*(T)_I^Γ`, written
multiplicatively by `Multiplicative`. So surjectivity says that every
`Γ`-invariant class in `X_*(T)_I` is `κ_T(t)` for some `t ∈ T(F)`.

**The map.** `torusKottwitzRational F T hT` is the Library's classical-epsilon
selection of a homomorphism satisfying `IsTorusKottwitzRestriction F T hT`. That
property says that for every `t ∈ T(F)`, the image of `κ t` under the
inclusion `torusInvariantInclusion F T` of `X_*(T)_I^Γ` into `X_*(T)_I` is the
constructed `K`-point map `torusKottwitz F F T hT` evaluated at
`GaloisPoint.extend F K T.toGrp (rationalCoeffEquiv F T.toGrp t)`, the point
`t` viewed in `T(K)`. This is KP's definition of `κ_T` on `T(k)` as the restriction of
`κ_{T_K}`. The map `torusKottwitz` is itself selected by the norm law of
Proposition 11.1.1 at every finite Galois splitting field `L/K`. The Library
proves both specifications: `torusKottwitzExistence` proves
`TorusKottwitzExistenceStatement` (module `Kottwitz.TorusMapProof`) and
`torusKottwitzDescent` proves `TorusKottwitzDescentStatement` (module
`Kottwitz.TorusMapDescentProof`). The descent statement includes
`IsTorusKottwitzRestriction F T hT (torusKottwitzRational F T hT)`. The
statement here is therefore about KP's map and not an arbitrary choice. It uses
the existing `torusKottwitzRational` and introduces no substitute map.

## What is not assumed

The proposition has no premise besides the local field `F`, the group scheme `T`
and `IsInducedTorus T`. In particular it supplies

* no surjectivity of `torusKottwitz` or of `torusKottwitzRational`;
* no chosen lift of a class in `X_*(T)_I^Γ` to `T(F)`;
* no decomposition of `T` into Weil restrictions of `𝔾_m`, and no Shapiro
  isomorphism for points or lattices;
* no compatibility of the Kottwitz map with restriction of scalars
  (KP Lemma 11.1.8).

All of these are left to a proof. No proof is given in this module.

The statement concerns only induced tori, as Corollary 11.1.9 does. KP's
Remark 11.1.7 says more generally, citing Corollary 11.7.2, that
`T(k)/T(k)^0 → (X_*(T)_I)^Γ` is an isomorphism for every `k`-torus when
`dim(f) ≤ 1`. This module does not state that more general assertion.

## Use

`ZExtensionRationalKernelReductionStatement` (module
`Langlands.Geometry.Building.Kottwitz.ZExtensionRationalKernelReduction`) has
the premise

```
∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (hT : IsInducedTorus T),
  Function.Surjective (torusKottwitzRational F T hT.isTorus)
```

which its documentation calls KP Corollary 11.1.9. A private compilation
checked that this premise is the present proposition, so a proof of
`InducedTorusKottwitzRationalSurjectivityStatement.{u}` can be passed for it
directly.

## Proof route in the source

KP's one-line proof reduces, by Lemma 11.1.8, to `T = 𝔾_m`. Implicitly it
writes an induced torus as a product of Weil restrictions `R_{ℓ/k} 𝔾_m` along
finite separable extensions `ℓ/k`. Lemma 11.1.8 identifies the Kottwitz map of
`R_{ℓ/k} S` on `k`-points with that of the `ℓ`-torus `S` on `ℓ`-points. For
`S = 𝔾_m` that map is identified with the normalized valuation of `ℓ^×`, which
is onto `ℤ`; this is the case the source calls obvious.

The Library proves the decomposition as `inducedTorusWeilDecomposition`
(module `Langlands.GroupScheme.Torus.InducedWeilDecompositionProof`). A proof of
this statement still has to supply the restriction-of-scalars comparison of
Lemma 11.1.8, or another argument, and the transport of `torusKottwitzRational`
along isomorphisms and finite products.
