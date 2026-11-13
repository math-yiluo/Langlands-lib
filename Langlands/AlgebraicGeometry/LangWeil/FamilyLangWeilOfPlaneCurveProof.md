# Dimension induction for uniform family Lang–Weil

Author: Worker 3519 (proof draft in the shared draft of Task 3519, revision 2);
submitted unchanged by Worker 1383 for Task 5840.

`Langlands.AlgebraicGeometry.LangWeil.familyLangWeilOfPlaneCurve.{u}` proves
`Langlands.AlgebraicGeometry.LangWeil.FamilyLangWeilOfPlaneCurveStatement.{u}`.
It assumes the plane-curve estimate `PlaneCurveHasseWeilStatement.{u}` and
concludes the existing uniform family estimate `FamilyLangWeilStatement.{u}`,
that is `FamilyLangWeilInDimension.{u} d` for every natural fibre dimension `d`,
in the same arbitrary universe `u`.

The proof first establishes `FamilyLangWeilInDimension (n + 1)` for every
natural number `n` by induction on `n`:

- At `n = 0` (fibre dimension 1), `familyLangWeilCurve` is applied to the
  supplied plane-curve estimate and the proved `familyPointUpperBound`.
- At `n + 1` (fibre dimension `n + 2`), `familyLangWeilSlicing` is applied to
  the proved `BertiniGenericHyperplane.bertiniGenericHyperplaneStatement`, the
  same `familyPointUpperBound`, and the induction hypothesis for dimension
  `n + 1`.

A final case split on the requested dimension `d` uses `familyLangWeilZero` when
`d = 0` and the positive-dimensional induction when `d = n + 1`.

Provenance: internal composition of the published dimension reductions
(`familyLangWeilZero`, `familyLangWeilCurve`, `familyLangWeilSlicing`) and the
published proofs of their two geometric and counting premises
(`bertiniGenericHyperplaneStatement`, `familyPointUpperBound`). No new estimate
or geometric argument is introduced. The plane-curve estimate remains an
explicit hypothesis; this theorem alone does not prove unconditional Lang–Weil.
