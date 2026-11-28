# The summand-to-realization theorem for GL_n from the density input

`Langlands.Automorphic.GroupSchemeFunctions.GeneralLinearCuspidalSummandRealizationFromDensityStatement`
is the implication

`GeneralLinearSummandFormsDenseStatement.{u} → GeneralLinearCuspidalSummandRealizationStatement.{u}`.

The premise is the published density input. For every nonzero, closed, `πc`-invariant and
minimal subspace `P` of the full almost-everywhere cuspidal `L²` space of the positive-central
rational quotient of `GL_{r+1}`, the classes of the attached stable cusp forms are dense in `P`.
The conclusion is the unchanged `GeneralLinearCuspidalSummandRealizationStatement`, the summand-to-realization direction of
Getz–Hahn, *An Introduction to Automorphic Representations*, Springer GTM 300 (2024),
Theorem 9.7.3, pp. 265–267 (PDF pp. 277–279).

## Implemented proof

`generalLinearCuspidalSummandRealizationFromDensity` applies the published
`generalLinearCuspidalSummandRealizationReduction` to the premise and two proved inputs.

- `generalLinearSummandFormsEnveloping` proves differential stability
  (`GeneralLinearSummandFormsEnvelopingStatement`).
- `generalLinearSummandFormsIrreducible` proves algebraic irreducibility
  (`GeneralLinearSummandFormsIrreducibleStatement`). Its own Markdown describes the proof.

## Scope

This module proves a conditional implication. Its premise, the density statement
`GeneralLinearSummandFormsDenseStatement` (module
`Langlands.Automorphic.GeneralLinearCuspidalSummandRealizationReduction`), is only the
hypothesis of that implication: the module neither proves nor otherwise assumes it. This module
proves neither the converse direction of Theorem 9.7.3 nor any density statement.

The Library proves the premise and the conclusion in other modules:

- `generalLinearSummandFormsDense` (module
  `Langlands.Automorphic.GeneralLinearSummandFormsDenseProof`) proves
  `GeneralLinearSummandFormsDenseStatement`;
- `generalLinearCuspidalSummandRealization` (module
  `Langlands.Automorphic.GeneralLinearCuspidalSummandRealizationProof`) proves
  `GeneralLinearCuspidalSummandRealizationStatement` unconditionally, by applying
  `generalLinearCuspidalSummandRealizationFromDensity` to `generalLinearSummandFormsDense`.
