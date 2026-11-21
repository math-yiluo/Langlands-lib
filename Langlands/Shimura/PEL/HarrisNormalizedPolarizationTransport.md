# Invariance of primitive Harris polarizations under isomorphism

This internal module chooses the primitive polarization of a polarized Harris
action and shows that the choice is compatible with the comparison of
polarizations in the ordinary Harris relation. It adds no literature
assertion. Positivity of polarization ratios enters only as the explicit
hypothesis `PolarizationRayPositivityStatement`, a separately staged
statement target.

## Dual pullback as transport

The ordinary relation `TateNormalizedCMOrdinaryRelated` compares the
polarization of `X` with the integral dual pullback
`integralDualPullbackHom … g.hom (polarization of Y)` along an actual
isomorphism `g`. `harrisDualPullback_eq_transportMap` records that this
pullback is, by definition, the published `DualWitness.transportMap` for the
published dual witnesses `PolarizedWeilLevel.PolarizedAction.dualWitness` of
the two actions.

## The chosen primitive polarization

The section assumes a connected locally noetherian base on which every
positive integer is a unit, and an algebraically closed point `s`.

`harrisPrimitivePolarizationOf X eta hn` is the definition of the module. For
a normalized frame `eta` of `X` at `s`, it is the primitive polarization given
by `exists_harrisPrimitivePolarization`, chosen with `Classical.choose`. Only
the existence proposition enters the choice, and it does not mention the
frame, so the chosen map does not depend on the frame.
`harrisPrimitivePolarizationOf_spec` records that it satisfies
`HarrisPrimitivePolarization`. `harrisPrimitivePolarizationOf_eq` shows that
every primitive polarization of `X` equals it, by
`harrisPrimitivePolarization_unique`, given the finite-étale torsion
statement.

## Compatibility with integral multiples

`harrisPrimitivePolarization_pullback` assumes
`PolarizationRayPositivityStatement` and positive relative dimension of the
abelian scheme of `X`. Suppose the dual pullback of the polarization of `Y`
along `g` and the polarization of `X` carry
`Rationalization.IntegralMultipleData` for some rational `q`, as in the
ordinary relation. Then the dual pullback of the primitive polarization of `Y`
is the primitive polarization of `X`. The proof is
`DualWitness.transportMap_eq_of_primitive` applied to the published dual
witnesses, the two published polarization properties and the integral
multiple equation. `harrisPrimitivePolarizationOf_pullback` restates this for
the chosen primitive polarizations.

This module does not prove `PolarizationRayPositivityStatement`, show that the
primitive polarization is a polarization, compute its degree, or treat level
structures and base change.
