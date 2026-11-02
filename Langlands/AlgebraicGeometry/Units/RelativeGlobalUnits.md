# Actual relative global units

This is an internal construction from the ordinary scheme pullback and
global-section functors. It applies to any morphism of schemes `f : X ⟶ S`
in universe `u`. It uses the published `Picard.relativeSpace f`, whose value
at `T : Over S` is the actual categorical fibre product `T.left ×_S X`.
There are no affineness, compactness, nonemptiness or reducedness hypotheses.

`sections f T` is the group `Γ(T.left ×_S X, ⊤)ˣ`. For `h : T ⟶ U`,
`restriction f h` is the unit-group homomorphism induced by
`((Picard.relativeSpace f).map h).appTop`. The theorem `restriction_val`
gives its formula on the underlying global functions. The identity and
composition equations are `restriction_id` and `restriction_comp`; they
follow from functoriality of the actual fibre product and ordinary
scheme pullback of global functions.

`groupPresheaf f` packages these groups and homomorphisms as a presheaf
with values in `CommGrpCat`. `presheaf f` gives the underlying
`AlgebraicSpace.Presheaf S`, with the usual `ULift` to `Type (u+1)`.
The evaluation and restriction formulas are `presheaf_obj` and
`presheaf_map_down`.

Given an actual unit `a` on `U.left ×_S X`,
`fromUniversalUnit f U a` is a natural transformation from the actual
lifted scheme Yoneda presheaf of `U` to `presheaf f`. Its component at
a point `h : T ⟶ U` is the pullback of `a` along
`(Picard.relativeSpace f).map h`. This is the equation
`fromUniversalUnit_app`; `fromUniversalUnit_naturality` states the
corresponding composition equation. The construction uses that unit as
data and does not use any representation theorem. This module does not
assert that this natural transformation is an isomorphism.
