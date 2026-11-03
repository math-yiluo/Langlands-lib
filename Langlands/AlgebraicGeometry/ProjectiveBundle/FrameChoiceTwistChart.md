# Chart compatibility of degree-one comparisons for frame families

This derived construction proves the missing chart compatibility for the
line bundles and frame comparisons of `ProjectiveBundle.FrameChoiceTwist`.
It uses the same scheme `S`, module `M`, natural number `n`, and hypothesis
`hM : IsLocallyFreeOfRank M (n + 1)`. The frame families are genuine choices
of local bases of `M` on every frame-bearing open. No additional gluing or
composition hypothesis is imposed on these families.

## The proved chart equation

Fix frame families `b,c` and a frame-bearing open `U`. Write `j_b,j_c` for
the charts of `familyCocycle hM b` and `familyCocycle hM c`, write `f_bc`
for `(frameChoiceIso hM b c).hom`, and set

- `A_bc = globalLinearAction n (familyCoordinate b c U)`;
- `L_b = (familyTwistOne hM b).obj`, and likewise `L_c`;
- `tau_bc = (frameChoiceTwistIso hM b c).hom`;
- `eta_b = (familyTwistChartIso hM b U).hom`, and likewise `eta_c`;
- `rho_bc = (LinearSystem.globalLinearActionTwistIso U.val.toScheme n
  (familyCoordinate b c U)).hom`.

The declaration `frameChoiceTwistIso_chart` is a checked proof of

```text
j_b^*(tau_bc) ; eta_b
  = squarePullbackIso(j_c,j_b,A_bc,f_bc).hom ; A_bc^*(eta_c) ; rho_bc.
```

Here semicolons denote categorical composition, the square is the published
`chart_frameChoiceIso_hom hM b c U`, and all pullbacks are pullbacks of
scheme modules. Thus the equation compares two maps from
`j_b^*(f_bc^* L_c)` to the standard degree-one module on the relative
projective space over `U`. Its left side restricts the global frame-family
comparison, and its right side applies the degree-one comparison for the
actual dual-frame coordinate change.

The Lean proof retains the explicit pullback-comparison form rather than
restating the equation with the abbreviations above. In detail, let
`j_0 = FrameBundle.chart hM U`, `N = (FrameBundle.twistOne hM).obj`,
`t_b = (toFrameBundleIso hM b).hom`, and
`iota = FrameBundle.twistOneModuleIso hM U`. Use analogous notation for
`c` and the fixed frame family `frame M n`. Then its exact left side is

```text
j_b^*(compHom(f_bc,t_c,t_b,N)) ;
  squarePullbackIso(j_0,j_b,A_b0,t_b,N).hom ;
  A_b0^*(iota.hom) ; rho_b0,
```

and its right side is

```text
squarePullbackIso(j_c,j_b,A_bc,f_bc,t_c^* N).hom ;
  A_bc^*(squarePullbackIso(j_0,j_c,A_c0,t_c,N).hom ;
    A_c0^*(iota.hom) ; rho_c0) ; rho_bc.
```

Each `compHom` and square receives the corresponding proved map equality.
The relative linear actions at `U.val.toScheme.toSpecΓ` used in the proof
are definitionally the displayed global linear actions. Expanding
`frameChoiceTwistIso`, `familyTwistChartIso`, and the isomorphism-composition
homs and reassociating gives the shorter equation above.

## Implemented proof

`chartSquare_compHom` proves the compatibility of canonical pullback
comparisons with two compatible chart squares. It normalizes all maps to
one common composite using the already published
`CommonSourceCocycle.square_normalize`, `inner_square_normalize`, and
`outer_square_normalize`. The remaining equality is `compHom_assoc`.

`chartTwist_transport` combines that equality with the naturality of
`compHom` and a local twist-composition law. It accepts the local law in
the raw `pullbackComp` and `pullbackCongr` form and converts it to
`compHom` before applying naturality. This lemma is a conditional generic
transport result; the final frame-family proof supplies its local law.

`LinearSystem.relativeLinearActionTwistIso_comp_named` proves that local
law for any three coefficient equivalences `e,f,g` with `e.trans f = g`
and any proof of the corresponding action composition. It applies
`linearChange_pullback_comparison_comp` directly to the comparison for
`g`. The section-coordinate identity follows from
`relativeLinearActionTwistIso_coordinate` and `e.trans f = g`.
It does not assume the twist-composition conclusion.

`LinearSystem.relativeLinearActionTwistIso_chart` applies
`chartTwist_transport` and this proved relative composition law while the
coefficient ring and base scheme are still arbitrary.
`familyRelativeLinearAction_comp` specializes action composition using
`familyCoordinate_trans`. The checked proof
`familyLinearActionTwist_comp` specializes the named relative twist law.
Finally, `frameChoiceTwistIso_chart` specializes the entire chart argument
to the frame families `b,c,frame M n`. Its inputs are the already proved
frame-chart squares and `FrameBundle.twistOneModuleIso`.

The three proof specializations are declared using `def` with inferred
proof types. They contain complete proof terms, not new assumptions or
Prop-valued statement placeholders. Inferring the types preserves the
coefficient-ring expression of the generic theorem; duplicating the
expanded restricted-scheme types causes expensive kernel conversions.
The local `linter.defProp` settings only suppress the naming-style warning
for these proof definitions. All proofs remain subject to ordinary kernel
checking, with finite default heartbeat limits.

## Provenance and scope

This is an internal consequence of the published frame-family,
tautological-line-bundle, pullback-coherence, and relative-linear-action
constructions imported by `FrameChoiceTwist`. No new literature assertion
is used. It completes chart compatibility under changes between frame
families on the existing frame-bearing opens. Comparisons between
different atlases, invariance under tensoring the source module by a line
bundle, cubic embeddings, and ordinary polarized moduli representability
are not proved here.
