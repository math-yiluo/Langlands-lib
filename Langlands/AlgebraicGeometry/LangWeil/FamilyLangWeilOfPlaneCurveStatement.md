# Uniform family Lang–Weil from the plane-curve estimate

Author: Worker 3519.

`Langlands.AlgebraicGeometry.LangWeil.FamilyLangWeilOfPlaneCurveStatement.{u}`
is the derived proposition

`PlaneCurveHasseWeilStatement.{u} → FamilyLangWeilStatement.{u}`.

The hypothesis is the Library's precise Schmidt plane-curve estimate: for every
finite field in universe `u` and every absolutely irreducible polynomial with
positive degree in both variables, the stated square-root error bound holds
above its degree-dependent field-size threshold. The conclusion is the existing
uniform family estimate in every natural fibre dimension. It retains the full
scope of `FamilyLangWeilStatement`: a finite-type base over the integers, a
locally finite-type quasi-compact morphism with geometrically irreducible fibres
of the specified pure dimension, and one positive real constant for all finite
fields and all rational points of the base. Separatedness, smoothness and
reducedness are not added.

## Provenance and intended deduction

Provenance: derived from published Library statements and proofs. This module
introduces no new formulation of a literature theorem. The mathematical sources
and their translations are documented in the paired Markdown of the imported
`PlaneCurveHasseWeilStatement` and `FamilyLangWeilStatement`, and of the three
dimension reductions below.

The deduction uses these published declarations, all in
`Langlands.AlgebraicGeometry.LangWeil`:

- `familyLangWeilZero : FamilyLangWeilZeroStatement` supplies dimension zero.
- `familyLangWeilCurve : FamilyLangWeilCurveStatement` supplies dimension one
  from the plane-curve estimate and `FamilyPointUpperBoundStatement`.
- `familyLangWeilSlicing : FamilyLangWeilSlicingStatement` advances dimension
  `d + 1` to dimension `d + 2`, using `BertiniGenericHyperplaneStatement` and
  `FamilyPointUpperBoundStatement`.
- `familyPointUpperBound` proves the latter upper-bound proposition, and
  `BertiniGenericHyperplane.bertiniGenericHyperplaneStatement` proves the
  generic Bertini proposition.

Thus induction gives all positive dimensions from the curve case; the separate
zero case completes `FamilyLangWeilStatement`. The only remaining hypothesis
in this implication is the plane-curve estimate.

This is a statement module and contains no proof. In particular, it does not
assert that the plane-curve estimate or the unconditional family estimate has
been proved. It supplies a focused target for the final dimension-induction
assembly, without changing either imported proposition.
