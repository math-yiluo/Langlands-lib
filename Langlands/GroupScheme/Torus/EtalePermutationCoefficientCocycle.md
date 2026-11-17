# Coherence of coefficient transitions from split charts

This internal derived module compares the chart transitions on all unit-valued
tests and the coefficient maps glued from their local permutations.

`transitionUnits_coordinates` evaluates the target chart on the same original
group morphism whose source coordinates were supplied. It is the inverse law of
the source chart point equivalence. `transitionUnits_congr` compares tests on
different common bases when their two induced maps to the original chart bases
agree. `transitionUnits_comp` is the three-chart cocycle on unit families: the
intermediate chart inverse recovers the same original group morphism.

`LocallyPermutes.coefficientDatum_formula` records the local unit formula for
the chosen overlap coefficient datum. `coefficientDatumAlong` pulls this datum
back along the actual fibre-product lift of any pair of equal-composite maps.
`coefficientDatumAlong_formula` proves its local unit formula by composing the
test with that lift and comparing the two original chart-base maps.

`coefficientEquivAlong_cocycle` proves that the actual glued algebra equivalences
satisfy the three-chart cocycle on any common scheme. The intersection-cover
composite datum and the direct datum both describe the direct unit transition,
so `Datum.equiv_eq_of_unitTransform` identifies their maps. `Datum.equiv_comp`
identifies the first map with the composite of the two given equivalences.

`transitionUnits_self` is the identity for a chart changed to itself.
`coefficientEquivAlong_self` derives the identity law for the glued algebra
equivalence on repeated chart maps by comparison with the one-open identity
datum. Neither proof requires a nonempty common base.

All schemes and indices lie in an arbitrary common universe. The coordinate
sets are finite but may be empty or have different ranks between charts. No
nonemptiness or affineness of the common base is assumed. This module does not
yet construct a multiplicative descent coaction or prove effective descent of
the Weil presentation.
