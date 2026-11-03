# Degree-one line bundles under changes of genuine frames

This is a derived construction from the published projective frame bundle,
its descended degree-one line bundle, and canonical module-sheaf pullback
comparisons. It uses no additional representability or gluing premise.

Let `S : Scheme.{u}`, let `M : S.Modules`, let `n : ℕ`, and assume
`hM : IsLocallyFreeOfRank M (n + 1)`. A `FrameFamily M n` assigns a genuine
local frame to every frame-bearing open. The published `familyBundle hM b`
is the actual projective scheme glued using the dual frames of such a
family `b`; `frameChoiceIso hM b c` is its actual comparison with the
scheme from `c`. Write

- `P_b = familyBundle hM b`;
- `f_bc = (frameChoiceIso hM b c).hom`;
- `t_b = (toFrameBundleIso hM b).hom : P_b ⟶ frameBundle M n hM`;
- `N = (FrameBundle.twistOne hM).obj`.

All schemes and module sheaves here are the existing concrete constructions.
There is no assumption that `M` is globally free.

## Actual bundles and comparisons

`familyTwistOne hM b` is the line bundle with underlying module `t_b^* N`.
Its local rank-one property is proved by preservation of local rank one
under pullback. Thus it is the actual line-bundle pullback of the fixed
frame bundle's degree-one bundle, constructed explicitly at the module
level.

`frameChoiceIso_hom_toFrameBundle` proves `f_bc ≫ t_c = t_b` from the
published composition theorem for frame choices. Consequently canonical
pullback composition constructs

`frameChoiceTwistIso hM b c : f_bc^* (t_c^* N) ≅ t_b^* N`.

`frameChoiceTwistLineIso` lifts this module isomorphism to an isomorphism
of the actual line bundles. Both constructions have exactly the displayed
local-freeness assumption and the two genuine frame families as inputs.

## Identity and global composition

`frameChoiceTwistIso_refl` identifies the comparison at identical frame
families with equality transport along `frameChoiceIso_refl` followed by
the canonical identity-pullback isomorphism. Identity pullback is retained
as a functor with its comparison isomorphism.

The generic helper `compIso_id_left_congr` proves this identity statement
by reducing to an identity scheme map, applying isomorphism extensionality,
and using `compHom_id_left`.

`frameChoiceTwistIso_comp` proves the composition equation

`f_bc^*((frameChoiceTwistIso hM c d).hom) ≫ (frameChoiceTwistIso hM b c).hom`

`= compHom f_bc f_cd f_bd (frameChoiceIso_hom_comp hM b c d) (t_d^* N)`

`  ≫ (frameChoiceTwistIso hM b d).hom`.

The Lean statement writes out the defining `compIso` expressions and the
underlying pullback module in this equation. These are exactly the bodies
of the named frame comparisons. This explicit form avoids expensive
conversions between the concrete module types during kernel checking.
The proof specializes the published `LineBundleFlatDescent.compIso_assoc`
from `Modules/LineBundleFlatDescentStr`, in the reverse direction. It follows
from `compHom_assoc` after replacing isomorphism homs by `compHom`.
All map-factorization equalities are supplied by the published
`frameChoiceIso_trans`; no composition compatibility is assumed.

## Standard degree-one bundle on each chart

`familyCoordinate b c U` is the coordinate equivalence obtained from the
actual change of dual frames on the frame-bearing open `U`.
`familyCoordinate_trans` follows from `LocalFrame.change_trans` and
`ProjectiveSpace.coordinateBaseChange_trans`.
`familyLinearAction_comp` applies the published projective linear-action
composition theorem to this equality.

`familyChart_toFrameBundle` identifies the composite of the family chart
with `t_b` as the corresponding global linear action followed by the
fixed frame-bundle chart. It specializes `chart_frameChoiceIso_hom`.

`familyTwistChartIso hM b U` is an actual module-sheaf isomorphism from
the family-chart pullback of `familyTwistOne hM b` to
`(RelativeProjectiveSpace.twistOne U.val.toScheme n).obj`. Its three
factors are the canonical comparison for that chart square, the pullback
of `FrameBundle.twistOneModuleIso hM U`, and the existing
`LinearSystem.globalLinearActionTwistIso` for the actual dual-frame
coordinate change.

## Provenance and remaining scope

This unit is derived from `ProjectiveBundle.FrameChoice`,
`ProjectiveBundle.Tautological`, module pullback transport, and
`Picard.RigidifiedPullbackProofs`. The proof route is the explicit
pullback construction and its canonical associativity, rather than a new
descent argument for each family.

The compatibility equation for these chart isomorphisms when the frame
family changes remains a separate obligation. This unit also does not
compare different atlases, prove tensor-line invariance, construct a
cubic embedding or a Hilbert quotient, or prove
`LargeLevelRepresentabilityStatement`.
