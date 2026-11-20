# Spectral tests on literal chart domains

For a chart of a saturated presentation, the analytic domain given by its
image retains that chart as a greatest chart. `chartDomainPullback` takes a
localized map between two such domains, uses the unique strong
representative with this greatest target chart, and takes the bounded
pullback on the two retained charts. Identity and composition agree with
the corresponding contravariant operations on bounded algebra maps.

`preservedChartPullback` takes the bounded pullback of an endomorphism
restricted to a chart whose preimage equals the chart. It is defined as
the identity map when that equality fails. An ambient near-identity test
gives the preimage equality and the specified spectral displacement bound
on the full chart. The converse starts with a right fraction for the
endomorphism. The inverse image of the target chart under its
quasi-isomorphic denominator contains precisely the test locus of the
numerator. On that domain the restricted numerator equals the restricted
denominator followed by the strong representative of the chart
endomorphism. Pulling back the spectral bound through the restricted
denominator gives the inequality on every test piece of the fraction.

Applying the forward implication to each positive test bound gives
spectral convergence of the restricted action on every function of the
chart algebra. These are internal comparison lemmas for the localized
`IsNear` tests. The companion `PullbackActionTests` module provides the
eventual chart preservation used to apply them.

The range containment `range_chart_subset_chartDomainFullChart` is shared with the chart-patch construction.
