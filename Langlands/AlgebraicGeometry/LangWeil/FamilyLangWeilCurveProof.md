# The uniform Lang–Weil estimate for curve families

Author: Worker 158.

The theorem `Langlands.AlgebraicGeometry.LangWeil.familyLangWeilCurve` proves
the unchanged published proposition
`Langlands.AlgebraicGeometry.LangWeil.FamilyLangWeilCurveStatement.{u}`.
It derives the uniform estimate for geometrically irreducible families with
pure-dimension-one fibres from exactly the two hypotheses of that proposition:
`PlaneCurveHasseWeilStatement` and `FamilyPointUpperBoundStatement`.

The proof applies `familyLangWeilCurve_of_planeComparison` from the companion
`FamilyLangWeilCurvePlaneReduction` module to the Library theorem
`familyCurvePlaneComparison` from `FamilyCurvePlaneComparisonProof`.
The latter proves the geometric comparison for the full scheme-family scope,
including nonreduced fibres and inseparable generic geometry.

For a fixed family, the comparison gives one positive integer `B` bounding
both individual-variable degrees of a plane polynomial and its point-count
discrepancy from the actual fibre. The arithmetic reduction uses Schmidt's
bound for fields larger than `T = B + 9(B+1)^4` and the original upper bound
for the remaining fields. If `A` is the upper-bound constant, then
`C = (A+1)(T+1) + B + 2B^3 + 1` works uniformly for every finite field and
every rational base point. The companion Markdown explains both inequalities
and the conversion of pure fibre dimension to the dimension upper bound.

Provenance: internal composition of proved Library geometry with the numerical
argument described above. The mathematical motivation and original literature
are documented in the unchanged statement's paired Markdown. The final theorem
adds no hypothesis to the published implication and assumes no additional
point-count estimate.
