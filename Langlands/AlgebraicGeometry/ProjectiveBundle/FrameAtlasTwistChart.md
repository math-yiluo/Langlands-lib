# Degree-one comparison in a common chart of genuine frame atlases

This derived unit proves the common-open chart compatibility equation for the
actual degree-one line bundles and comparisons of `FrameAtlasTwist`. It uses
the generic chart transport and the proved relative linear-action composition
law in `FrameChoiceTwistChart`. No external geometric assertion is invoked.

Let `S : Scheme.{u}`, `M : S.Modules`, and `n : ℕ`. Fix genuine frame atlases
`a,b : FrameAtlas M n`, a hypothesis
`hM : IsLocallyFreeOfRank M (n + 1)`, and an open `U : S.Opens` with
`ha : U ∈ a.opens` and `hb : U ∈ b.opens`. All charts below have the same
actual source `RelativeProjectiveSpace U.toScheme n`.

## The chart equation

Write

- `j_a = a.cocycle.chart ⟨U,ha⟩` and `j_b = b.cocycle.chart ⟨U,hb⟩`;
- `f_ab = (a.comparisonIso hM b).hom`;
- `A_ab = globalLinearAction n (a.changeCoordinate b U ha hb)`;
- `L_a = (a.twistOne hM).obj` and `L_b = (b.twistOne hM).obj`;
- `tau_ab = (a.comparisonTwistIso hM b).hom`;
- `eta_a = (a.twistChartIso hM ⟨U,ha⟩).hom`, and likewise `eta_b`;
- `rho_ab = (LinearSystem.globalLinearActionTwistIso U.toScheme n
  (a.changeCoordinate b U ha hb)).hom`.

The checked proof `comparisonTwistIso_chart` states, in explicit canonical
pullback form, the equation

```text
j_a^*(tau_ab) ; eta_a
  = squarePullbackIso(j_b,j_a,A_ab,f_ab).hom ; A_ab^*(eta_b) ; rho_ab.
```

The square uses the proved equation `a.chart_comparisonIso_hom hM b U ha hb`.
Semicolons mean categorical composition. Both sides are maps from
`j_a^*(f_ab^* L_b)` to the standard degree-one module on
`RelativeProjectiveSpace U.toScheme n`. The equation therefore identifies the
restriction of the global line-bundle comparison with the comparison given by
the actual change between the two dual frames on `U`.

For the exact expanded form, put
`N = (FrameBundle.twistOne hM).obj`,
`t_a = (a.toFrameBundleIso hM).hom`, and likewise `t_b`.
Let `j_0 = FrameBundle.chart hM (a.toFrameOpen ⟨U,ha⟩)` and
`iota = FrameBundle.twistOneModuleIso hM (a.toFrameOpen ⟨U,ha⟩)`.
Write `A_a0` for the linear action of `a.comparisonCoordinate ⟨U,ha⟩`,
and similarly `A_b0`; write `rho_a0,rho_b0` for their degree-one comparisons.
The exact left side is

```text
j_a^*(compHom(f_ab,t_b,t_a,N)) ;
  squarePullbackIso(j_0,j_a,A_a0,t_a,N).hom ;
  A_a0^*(iota.hom) ; rho_a0,
```

and the right side is

```text
squarePullbackIso(j_b,j_a,A_ab,f_ab,t_b^* N).hom ;
  A_ab^*(squarePullbackIso(j_0,j_b,A_b0,t_b,N).hom ;
    A_b0^*(iota.hom) ; rho_b0) ; rho_ab.
```

Every `compHom` and square is supplied its proved map equality. In the Lean
proof, each action is written as `linearAction U.toScheme.toSpecΓ` with its
coefficient equivalence; these are definitionally the displayed global linear
actions. The two `toFrameOpen` values obtained using `ha` and `hb` have the
same open and differ only in proofs, so they are definitionally equal.
Expanding `comparisonTwistIso` and `twistChartIso`, replacing `compIso` homs
by `compHom`, and reassociating gives the shorter equation.

## Implemented proof and provenance

`changeCoordinate_relativeLinearAction_comp` proves
`A_ab ≫ A_b0 = A_a0`. It applies `linearAction_comp` and the already proved
`changeCoordinate_comparison`, whose coefficients come from transitivity of
genuine dual-frame changes.

`comparisonTwistIso_chart` specializes
`LinearSystem.relativeLinearActionTwistIso_chart` to the common-open
projective space and the three actual projective schemes `a.bundle`,
`b.bundle`, and `frameBundle M n hM`. All global and chart-square
factorizations are supplied by `comparisonIso_hom_toFrameBundle`,
`chart_comparisonIso_hom`, and `chart_toFrameBundleIso_hom`. The remaining
standard-chart identification is the constructed `FrameBundle.twistOneModuleIso`.
The generic result proves the needed local composition law and transports it
through these squares; no local twist law or chart compatibility premise is
added to the final proof.

The final declaration is a complete inferred proof term introduced with `def`.
Its inferred type is an equality, rather than a new proposition awaiting a
proof. Preserving the explicit coefficient ring avoids duplicating expensive
restricted-scheme type conversions. The local `linter.defProp` setting only
suppresses a style warning; the proof uses ordinary kernel checking.

The unit is an internal consequence of the imported module-pullback,
relative-linear-action, genuine-frame and degree-one constructions. It proves
compatibility on an open belonging to both given bases. It does not assert a
common-refinement theorem for arbitrary distinct bases, invariance under
tensoring with a line bundle, a relative cubic embedding, a Hilbert quotient,
or `LargeLevelRepresentabilityStatement`.
