# Open-immersion locality of relative differentials

`Langlands.Scheme.RelativeDifferentialsOpenImmersionIsIsoStatement.{u}` is a
`Prop`-valued definition quantifying over arbitrary schemes `X'`, `X`, `S'`,
and `S` in universe `u`, and every commuting diagram

```text
X' ──g──▶ X
│         │
f'        f
│         │
▼         ▼
S' ──b──▶ S
```

Here `g : X' ⟶ X` and `b : S' ⟶ S` are open immersions, and
`w : g ≫ f = f' ≫ b` is any proof of commutativity. The conclusion is
`IsIso (relativeDifferentialsSquareMap g b w)` for the existing canonical map

```text
(Scheme.Modules.pullback g).obj (relativeDifferentials f)
  ⟶ relativeDifferentials f'.
```

The imported `RelativeDifferentialsBaseChange` module defines this exact map
using the actual sheaf of relative differentials, its universal derivation,
and the module pullback/pushforward adjunction. Its
`relativeDifferentialsSquareMap_fac` and
`relativeDifferentialsSquareMap_adjoint_app` characterize the map by its action
on universal differentials of local sections. The statement therefore concerns
invertibility of that map, rather than merely existence of an isomorphism
between the two sheaves. No construction or universal property is changed.

The only geometric hypotheses are the two open-immersion assumptions. There
is no requirement that the square be Cartesian, and no affine, smoothness,
reducedness, nonemptiness, or finiteness assumption. Empty open subschemes are
included. This module states the proposition; it does not prove it or assume
an instance of it.

## Source and interpretation

The original source is the Stacks Project, Morphisms §29.33,
[Lemma 29.33.3 (tag 01US)](https://stacks.math.columbia.edu/tag/01US), in
`01UM.html` of registered source
`stacks-relative-differentials-internal-hom-2026-10-21`, folder content SHA256
`9c075370ba97d8876785c5486425c6c661765e747452c026583f4dc51f1e1133`.
It identifies the restriction of relative differentials to an open subscheme
with the relative differentials for the restricted morphism, compatibly with
universal derivations. Its proof cites Modules §17.28,
[Lemma 17.28.5 (tag 08RQ)](https://stacks.math.columbia.edu/tag/08RQ), retained in
`08RL.html` of the same source. The canonical square map is the one described
in Lemma 29.33.8 (tag 01UV) of `01UM.html`.

The formulation here transports the open-subscheme statement along the
isomorphisms identifying arbitrary open immersions with their open images.
Restriction of module sheaves is identified with pullback using Mathlib's
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`. Compatibility
with universal derivations identifies the transported isomorphism with the
existing square map by its uniqueness property. These are the intended
mathematical justifications for the formulation, not proofs supplied here.

For arbitrary affine opens `V ⊆ X` and `U ⊆ S` with `f(V) ⊆ U`, the
associated maps `Spec Γ(X,V) ⟶ X` and `Spec Γ(S,U) ⟶ S` are open immersions.
The statement applies to their commuting square with the induced spectrum
map. Its intended use is to establish invertibility of the published
`relativeDifferentialsAffineChartSquareMap`, enabling comparison with affine
Kähler differentials on arbitrary charts. The separate affine Kähler
comparison and the proof of this locality statement remain further work.
