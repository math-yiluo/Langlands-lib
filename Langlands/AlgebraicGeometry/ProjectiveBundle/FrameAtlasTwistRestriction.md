# Restriction of degree-one comparisons on genuine frame atlases

This is derived infrastructure for the existing projective frame bundles.
It uses their actual dual-coordinate changes, canonical pullback comparisons,
and covering homogeneous coordinate sections. No additional geometric result
from an external source is invoked.

Let `S : Scheme.{u}`, `M : S.Modules`, `n : ℕ`, and `a : FrameAtlas M n`.
Assume `hM : IsLocallyFreeOfRank M (n + 1)`. The atlas specifies genuine
module frames on a topological basis of opens. Its actual projective scheme,
degree-one line bundle, and standard chart comparisons are the published
`a.bundle`, `a.twistOne hM`, and `a.twistChartIso hM U`.

For `h : U ⟶ V` in the ordered atlas cover, write `r` for
`a.cocycle.chartFunctor.map h`, and `jU`, `jV` for its two chart maps into
`a.bundle`. The existing transition equation is `r ≫ jV = jU`.
Write `L` for `(a.twistOne hM).obj`, and `OU`, `OV` for the standard
degree-one modules on the two relative projective spaces.

## Actual restriction comparison

`twistRestrictionIso hM h` is the actual isomorphism

`r* (jV* L) ≅ OU`.

It pulls back the existing `a.twistChartIso hM V` and follows it by the
existing full coordinate transition `a.cocycle.chartTwistIso h`.
`twistChartIso_restrict` proves the restriction equation

`r*((a.twistChartIso hM V).hom) ≫ (a.cocycle.chartTwistIso h).hom`

`= compHom r jV jU (a.cocycle.transition_chart h) L`

`  ≫ (a.twistChartIso hM U).hom`.

Thus the larger chart's comparison followed by the actual transition agrees
with canonical composition of pullbacks followed by the smaller chart's
comparison. `twistRestrictionIso_hom` states this same formula for the
constructed nested-chart isomorphism.

## Coordinate square

`comparisonCoordinate_square` proves that the atlas restriction followed by
the larger chart's change to its fixed frame equals the smaller chart's
change to its fixed frame followed by the fixed-frame restriction.
The proof uses base change and composition of global linear actions and
the published `comparisonCoordinate_compatible` matrix identity.

`chartTwistIso_comparison_square` lifts this actual scheme square to the
four degree-one comparison maps: the atlas restriction, fixed-frame
restriction, and the two changes to fixed coordinates.
Its proof supplies the existing bundled `chartTwistData` for the two
restrictions, together with their actual matrices and coefficient pullback.
It uses the generic result
`LinearSystem.relativeAction_twistedSquare_of_coordinateData`.
The latter keeps arbitrary coefficient rings and base schemes and uses
the constructed relative linear-action degree-one isomorphisms.

The underlying
`LinearSystem.linearChange_pullback_comparison_twistedSquare` allows
arbitrary line bundles on two schemes, four module comparison maps with
specified linear coordinate laws, and compatible matrices after coefficient
base change. The coordinate sections on the first line bundle must have
trivialization opens covering the scheme. Covering-section extensionality
reduces the conclusion to those sections; the coefficient-base-change
formula and composition of linear coordinate changes then give the result.
`chartTwist_comparison_criterion` specializes this arbitrary-map criterion
to the two frame-atlas charts and their prescribed matrices.

`LinearSystem.PullbackSquareCompatible.reverse` exchanges the two paths
of a compatible square using the inverse canonical square comparison.
It applies to arbitrary schemes and module sheaves.

## Canonical pullback transport

In `RefinedPullbackComparison`,
`normalize_local_restrict_between` generalizes the published
`normalize_local_restrict` calculation to arbitrary target modules on
the two source charts. These targets need not be pullbacks of a single
global module. Its hypotheses retain compatible chart scheme squares,
the restriction equation for the fixed-chart comparisons, and the square
equation for the local maps. The proof reverses the canonical square,
uses `normalize_refine`, and applies `compHom_assoc`.

`comp_normalize_eq_square` identifies outer composition followed by
normalization with the canonical square comparison followed by pullback
of the piece isomorphism. This is `CommonSourceCocycle.square_normalize`
followed by cancellation of the composition comparison.
`twistChartIso_hom_normalize` applies it to express the existing frame-atlas
chart isomorphism in normalized form.

Finally, `twistChartIso_restrict` applies
`normalize_local_restrict_between` with the actual map from the atlas
bundle to the fixed frame bundle. The fixed-frame restriction equation
is the published `FrameBundle.twistOneModuleIso_restrict`. The other
compatibility input is the reversed
`chartTwistIso_comparison_square`, already proved from the actual
coordinate data. No new compatibility premise is imposed on the atlas.

## Scope

These results supply restriction of the existing degree-one comparisons
on every genuine frame atlas. They do not yet glue the tensor-line
comparison globally, construct cubic embeddings or Hilbert quotients,
or prove `LargeLevelRepresentabilityStatement`.
