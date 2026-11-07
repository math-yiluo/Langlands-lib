# Algebraic-closure reduction for the supplied split Steinberg product

This is an internal reduction for the published
`SplitSteinbergQuotientStatement.{u}`. It uses the actual supplied-data transport
and quotient-isomorphism equivalence from `SteinbergFieldBaseChange` and the
existing proposition `IsSimplyConnectedAlgebraicClosureAscentStatement` from
`SimplyConnected.GeometricReduction`. It makes no independent claim from the
literature.

`SplitSteinbergQuotientAlgClosedStatement.{u}` is the restriction of the full
statement to algebraically closed fields. Its only additional field instance is
`IsAlgClosed k`. It retains the arbitrary universe `u`, the actual affine group
scheme, the supplied split pinning, the existing central-isogeny definition of
`IsSimplyConnected`, every rank and ordering, every supplied normalized root
parametrization, every supplied reflection representative, and the canonical
quotient map `ClassFunctions.rho G`. The conclusion remains an isomorphism in
`Over (Spec k)`. No characteristic restriction or alternative quotient is used.
The definition asserts no existence of the supplied data.

The theorem `splitSteinbergQuotientAlgClosed_of_splitSteinbergQuotient` restricts
the full statement by specialization. It has no ascent hypothesis.

The converse theorem `splitSteinbergQuotient_of_algClosed` has two explicit
inputs: simple-connectedness ascent to an algebraic closure and
`SplitSteinbergQuotientAlgClosedStatement.{u}`. For an arbitrary field `k`, actual
group `G`, pinning `p` and supplied data `e`, `x`, `n`, it sets
`K = AlgebraicClosure k` and takes the actual pullback group `GK`. Affineness is
preserved by this pullback. The ascent input gives `IsSimplyConnected GK`, and
`p.baseChange` gives the transported split pinning. The algebraically closed
input then applies to the transported original order, maps and representatives:
`fieldBaseChangeOrder e`, `fieldBaseChangeRootMaps x` and
`fieldBaseChangeRepresentatives n`. Finally,
`isIso_steinbergQuotient_baseChange_iff` returns the quotient-isomorphism
property for the exact original product and canonical quotient over `k`.
Algebraicity of `K/k` is available for the pinning transport, and the published
quotient descent uses faithful flatness. The original field may therefore be
finite or imperfect and may have positive characteristic.

The final theorem `splitSteinbergQuotient_iff_algClosed` combines the two
directions, retaining the explicit ascent input.

This module does not prove the algebraically closed statement or
simple-connectedness ascent. In particular, the latter is not inferred just
from pullback preservation of central isogenies: an arbitrary isogeny over an
algebraic closure need not descend to the original field. Both displayed inputs
remain obligations before this reduction proves the original target.
`SplitSteinbergQuotientStatement` and its imported pairs remain unchanged, and
the target itself acquires no premise.
