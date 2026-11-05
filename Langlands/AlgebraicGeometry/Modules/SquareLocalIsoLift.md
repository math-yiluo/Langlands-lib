# Local lifts of compatible isomorphism pairs across a cube

This module builds local isomorphisms for the gluing step in
`TwoLegIsoGluing`. Each one lifts a pair of isomorphisms that is compatible
on a base square of schemes. The setting is a commuting square

```
Y₀ --i₁--> Y₁
|          |
i₂         j₁
v          v
Y₂ --j₂--> Y
```

with `w : i₁ ≫ j₁ = i₂ ≫ j₂`, two `Y`-modules `M` and `N`, and isomorphisms
`e₁ : j₁^* M ≅ j₁^* N` and `e₂ : j₂^* M ≅ j₂^* N` of ordinary module
pullbacks. The pair is *compatible on the base square* when

`i₁^*(e₁) ≫ squarePullbackIso j₂ i₁ i₂ j₁ w N
  = squarePullbackIso j₂ i₁ i₂ j₁ w M ≫ i₂^*(e₂)`.

Here `squarePullbackIso` is the published comparison
`i₁^* j₁^* M ≅ i₂^* j₂^* M` of iterated ordinary pullbacks.

No closedness, nilpotence, flatness or field hypothesis is assumed anywhere.
Nothing is stated about line bundles; `M` and `N` are arbitrary modules,
except that the final lemma assumes both are trivial after pullback along `t`.

Namespace: `Langlands.Scheme.Modules.SquareLocalIsoLift`.

## Associativity of composite comparisons

The imported `LineBundleFlatDescent.compIso_assoc` is the `compIso`
form of the published `compHom_assoc`. Given
`a : X ⟶ Y`, `b : Y ⟶ Z`, `c : Z ⟶ W` and morphisms `ab`, `bc`, `abc` with
`a ≫ b = ab`, `b ≫ c = bc`, `ab ≫ c = abc` and `a ≫ bc = abc`, it says that the
two composite comparisons `a^* b^* c^* N ≅ abc^* N`, through `ab^* c^* N` and
through `a^* bc^* N`, agree. It has the `@[reassoc]` attribute.

## One face of a cube

The variables are morphisms `t : T ⟶ Y`, `s : T₁ ⟶ T`, `ι : T₀ ⟶ T₁`,
`g : T₁ ⟶ Y₁`, `g₀ : T₀ ⟶ Y₀`, `i : Y₀ ⟶ Y₁` and `j : Y₁ ⟶ Y`, with
commuting squares `h : s ≫ t = g ≫ j` and `k : ι ≫ g = g₀ ≫ i`.

- `legIso t s ι g g₀ i j h k M` is the isomorphism
  `ι^* s^* t^* M ≅ g₀^* i^* j^* M`. It applies `ι^*` to
  `squarePullbackIso j s g t h M` and then uses
  `squarePullbackIso i ι g₀ g k (j^* M)`.
- `localIso t s g j h e` transports `e : j^* M ≅ j^* N` to
  `s^* t^* M ≅ s^* t^* N`. It is the composite of
  `squarePullbackIso j s g t h M`, the pullback `g^*(e)`, and the inverse of
  `squarePullbackIso j s g t h N`.
- `localIso_legIso` (with `@[reassoc]`) is naturality:
  `ι^*(localIso … e) ≫ legIso … N = legIso … M ≫ g₀^*(i^*(e))`. The proof
  uses the published `squarePullbackIso_naturality` for the square `k`.
- `compatibleAt_of_localIso` takes `E : t^* M ≅ t^* N` with
  `s^*(E) = localIso t s g j h e`. It concludes the published predicate
  `LineBundleIsoDescent.CompatibleAt j e t E.hom g s h`, which is
  compatibility at the square `h`.
- `compatible_of_isPullback` strengthens this when `P : IsPullback g s j t`
  holds, so that `T₁` is the fibre product of `j` and `t`. If
  `s^*(E) = localIso t s g j P.w.symm e`, then
  `LineBundleIsoDescent.Compatible j e t E.hom` holds. This is compatibility
  at every commuting square over `j` and `t`. The proof factors an arbitrary
  square through `P.lift` and applies the published
  `LineBundleIsoDescent.compatibleAt_precomp`.

## A commuting cube

Now take the base square above together with a top square

```
T₀ --ι₁--> T₁
|          |
ι₂         s₁
v          v
T₂ --s₂--> T
```

with `wT : ι₁ ≫ s₁ = ι₂ ≫ s₂`. The two squares are joined by `t : T ⟶ Y`,
`g₁ : T₁ ⟶ Y₁`, `g₂ : T₂ ⟶ Y₂` and `g₀ : T₀ ⟶ Y₀`, and the side faces commute:
`h₁ : s₁ ≫ t = g₁ ≫ j₁`, `h₂ : s₂ ≫ t = g₂ ≫ j₂`, `k₁ : ι₁ ≫ g₁ = g₀ ≫ i₁` and
`k₂ : ι₂ ≫ g₂ = g₀ ≫ i₂`.

- `cube_coherence` says that the two face comparisons are compatible with the
  top and bottom square comparisons:
  `squarePullbackIso s₂ ι₁ ι₂ s₁ wT (t^* M) ≫ legIso (face 2) M
    = legIso (face 1) M ≫ g₀^*(squarePullbackIso j₂ i₁ i₂ j₁ w M)`.
  The proof cancels a composite comparison into `((ι₁ ≫ s₁) ≫ t)^* M`. It
  expands every square comparison with the published
  `squarePullbackIso_hom_eq_compIso`, and closes the goal with six instances
  of `compIso_assoc`.
- `localIso_compatible` says that a pair `(e₁, e₂)` compatible on the base
  square transports to a pair compatible on the top square. Its hypothesis
  `he` is base-square compatibility as displayed above. Its conclusion is
  `ι₁^*(localIso t s₁ g₁ j₁ h₁ e₁) ≫ squarePullbackIso s₂ ι₁ ι₂ s₁ wT (t^* N)
    = squarePullbackIso s₂ ι₁ ι₂ s₁ wT (t^* M) ≫ ι₂^*(localIso t s₂ g₂ j₂ h₂ e₂)`.
  The proof uses `cube_coherence` for `M` and `N` together with
  `localIso_legIso`.

## The local lift

`exists_compatible_lift` takes the cube data above, the isomorphisms `e₁`,
`e₂` and the base-square compatibility `he`. It also assumes:

- `P₁ : IsPullback g₁ s₁ j₁ t` and `P₂ : IsPullback g₂ s₂ j₂ t`, so both side
  faces are cartesian;
- `hT : IsPullback s₁.appTop s₂.appTop ι₁.appTop ι₂.appTop`, so the
  global-section rings of the top square form a pullback of commutative rings;
- trivializations `τ : t^* M ≅ 𝒪_T` and `σ : t^* N ≅ 𝒪_T`.

It concludes that there is `E : t^* M ≅ t^* N` with
`LineBundleIsoDescent.Compatible j₁ e₁ t E.hom` and
`LineBundleIsoDescent.Compatible j₂ e₂ t E.hom`. The proof applies
`SquareTrivialIsoDescent.existsUnique_iso` (from the imported module
`Langlands.AlgebraicGeometry.Modules.SquareTrivialIsoDescent`) to the top
square, with
the transported pair `localIso … e₁` and `localIso … e₂`. Their top-square
compatibility is `localIso_compatible`. That gives `E` with
`s₁^*(E) = localIso … e₁` and `s₂^*(E) = localIso … e₂`, and
`compatible_of_isPullback` for `P₁` and `P₂` turns these into the two
compatibility statements.

In the intended use, `t` is an open immersion trivializing both modules,
`s₁` and `s₂` are the inverse images of that open, and `hT` is a ring
pullback of sections over the restricted square. This module then supplies
only the local-existence input `hlocal` of
`TwoLegIsoGluing.existsUnique_iso_of_local`. That theorem has two further
hypotheses: a common trivializing open cover of `M` and `N`, and
`hU : TwoLegIsoGluing.UnitsJointlyInjectiveOnOpens j₁ j₂`. The second
quantifies over every open immersion into the base, not only over the chosen
cover charts, and this module neither proves nor implies it. A ring pullback
on the cover charts alone does not give it. So joint unit injectivity has to
be established separately for the intended square. For example,
`TwoLegIsoGluing.unitsJointlyInjectiveOnOpens_of_affine` reduces it to affine
open immersions. Only with all three inputs does
`existsUnique_iso_of_local` glue a global isomorphism `M ≅ N` whose
pullbacks along `j₁` and `j₂` are `e₁` and `e₂`.

## Provenance

This is internal infrastructure. It is the standard base-change argument for
ordinary pullbacks around a commuting cube, built from published interfaces:
`squarePullbackIso`, `compIso`, `compHom_assoc`,
`squarePullbackIso_hom_eq_compIso`, `squarePullbackIso_naturality`, the
`LineBundleIsoDescent` compatibility API, and the imported
`SquareTrivialIsoDescent.existsUnique_iso`. No cited source theorem is
formalized.
