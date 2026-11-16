# Proof of the finite-field quotient input for a twisted chamber through a fixed point

`unramifiedTwistedChamberQuotient` proves the published proposition
`Langlands.Geometry.Building.UnramifiedTwistedChamberQuotientStatement.{u}` exactly, at an
arbitrary universe `u`, with no added hypothesis. The statement's Lean/Markdown pair and
everything it imports are unchanged.

## Route

The proof is a one-line application of two published Library theorems.

1. The published conditional reduction `unramifiedTwistedChamberQuotientResidueReduction`
   (module `Langlands.Geometry.Building.UnramifiedTwistedChamberQuotientResidueReduction`)
   proves `UnramifiedTwistedChamberQuotientResidueReductionStatement.{u}`. That proposition is
   the implication

   `UnramifiedTwistedResidueQuotientStatement.{u} → UnramifiedTwistedChamberQuotientStatement.{u}`.

   Its proof does the following. It picks a Frobenius lift `φ` with dense powers and the
   arithmetic residue formula, using the published `exists_fixedField_arithmeticFrobenius`. It
   transports a presented chamber through the twisted action `z ↦ c φ • A.action φ z`, using the
   published Galois facet results. It then assembles `HasFiniteFieldChamberQuotient` from the
   transitivity and kernel clauses of the residue quotient statement.
2. The published theorem `unramifiedTwistedResidueQuotient` (module
   `Langlands.Geometry.Building.UnramifiedTwistedResidueQuotientProof`, Task 6572) proves
   `UnramifiedTwistedResidueQuotientStatement.{u}` unconditionally.

Applying the first to the second gives the target. The mathematical content is in those two
modules and their inputs, whose Markdown files record the source provenance (Kaletha–Prasad,
*Bruhat–Tits Theory: A New Approach*, 2023). The residue quotient statement is cited there to
Axiom 4.1.22 and Remark 4.1.23; its proof uses Proposition 8.3.1 and Corollary 8.4.12, and
the Frobenius descent input cites Fact 2.10.16.

## Downstream constraint

Neither ingredient uses, directly or through its imports, a proof of any of these consumers:
`UnramifiedTwistedGeneratorChamberStatement`,
`UnramifiedTwistedChamberThroughFixedPointStatement`, `UnramifiedTwistedChamberStatement`,
`LocalSimplyConnectedUnramifiedChamberStatement`,
`LocalSimplyConnectedUnramifiedIntegralTwistStatement`,
`LocalSimplyConnectedUnramifiedCocycleVanishingStatement`,
`LocalSimplyConnectedGaloisCocycleVanishingStatement` and
`LocalSimplyConnectedCocycleVanishingStatement`. The Markdown of
`UnramifiedTwistedResidueQuotientProof` records the same constraint for the residue quotient
proof. The reduction module imports only the two statements, `ChamberClosureOrbit`,
`GaloisFacetAction` and `SeparableUnramifiedFrobenius`.
