# Analytic action tests on chart subdomains

The greatest-chart pullback computes the point map of a localized
arrow between chart domains. For a nested pair of chart domains, the
bounded pullback of the actual localized inclusion is the original
atlas restriction. These identities use the strong representatives
with greatest target charts.

`preservedChartAut` restricts an ambient automorphism and its inverse to
a preserved chart, then pulls both maps back to bounded algebra maps.
Identity and composition of chart pullbacks prove that these maps are
mutual inverses. The definition uses the identity away from chart
preservation.

`eventually_isNear_of_chart_subset` applies represented-domain spectral
restriction to a smaller chart in a fixed parent chart. The point map
identifies preservation of the represented spectrum locus with
preimage equality on the smaller analytic chart. The two restricted
analytic maps commute with the nested chart inclusion by cancellation
of the domain mono. On bounded chart algebras this gives the defining
equation for the represented-domain section map, which uniquely
determines the whole bounded map. Its spectral estimate then proves
the ambient near-identity test. Thus charts containing every chart as
a subdomain suffice for continuity checks.

`IsContinuousAction.conjAut` transports continuity through a
localized analytic isomorphism. Its underlying homeomorphism pulls
back the compact test locus to a compact locus. The postcomposition
theorem reduces that test to finitely many tests on the original
space. On their common event, precomposing with the inverse
isomorphism gives the test for the conjugated action.

These lemmas relate the Library's full represented-domain
restrictions to its localized action tests, for use with the
affinoid patches of compact pullbacks.
