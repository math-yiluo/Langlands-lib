# Proof of the residue quotient at a twisted-fixed point for a Frobenius lift

`unramifiedTwistedResidueQuotient` proves the published proposition
`Langlands.Geometry.Building.UnramifiedTwistedResidueQuotientStatement.{u}` exactly, at an
arbitrary universe `u`, with no added hypothesis.

## Route

The proof is a short assembly of published Library theorems.

1. The published reduction `unramifiedTwistedResidueQuotientInputsReduction`
   (module `Langlands.Geometry.Building.UnramifiedTwistedResidueQuotientReduction`) proves
   `UnramifiedTwistedResidueQuotientInputsReductionStatement.{u}`. That statement says the
   target follows from three propositions at universe `u`:
   - `UnramifiedParahoricModelStatement` (compatible full and neutral integral models over the
     maximal unramified integers for bounded apartment subsets, KP Proposition 8.3.1 setting),
   - `UnramifiedUpstairsRadicalRootGenerationStatement` (KP Corollary 8.4.12, upstairs),
   - `UnramifiedTwistedReductiveQuotientDescentStatement` (Frobenius descent of the reductive
     quotient of a twisted-stable model).
2. The second input is the published theorem `unramifiedUpstairsRadicalRootGeneration`.
3. The third input is the published theorem `unramifiedTwistedReductiveQuotientDescent`
   (module `Langlands.BruhatTits.IntegralModels.UnramifiedTwistedReductiveQuotientDescent`).
4. The first input is `unramifiedParahoricModel_of_torusInputs hModel hBound`. This published
   theorem in `UnramifiedParahoricModelConstruction` proves `UnramifiedParahoricModelStatement`
   from two torus propositions. Both are discharged inside the proof by published theorems:
   - `hLift : UnramifiedTorusNeutralSurjectivityStatement` is
     `unramifiedTorusNeutralSurjectivityAssembly` applied to `connectedGeneration` (KP Lemma
     A.4.26), `torusQuotientRationalSurjectivity`,
     `unramifiedTorusNeutralFiniteGeneration` and `torusSurjectionIsogenySection`;
   - `hBound : UnramifiedTorusConnectedBoundStatement` is
     `unramifiedTorusConnectedBoundAssembly` applied to `unramifiedTorusBoundedModel`, `hLift`
     and `unramifiedTorusNormPresentation`;
   - `hModel : UnramifiedTorusIwahoriModelStatement` is
     `unramifiedTorusIwahoriModelAssembly` applied to `IntegralModel.smoothHomExtension`,
     `unramifiedTorusBoundedModel`, `hBound` and `unramifiedTorusIwahoriConnectedImage`.

   The same discharge of the torus inputs appears in the published
   `unramifiedSpecialApartmentChamber_of_connectedGeneration`. There it is conditional on
   connected generation, which the Library now proves as `connectedGeneration`.

The mathematical content (the model at the point, the reductive quotient and its kernel, the
twisted action, Frobenius descent and chamber transitivity) is in the reduction module and its
inputs. Their Markdown files record the source provenance (Kaletha–Prasad, *Bruhat–Tits Theory:
A New Approach*, 2023).

## Downstream constraint

The proof does not use, directly or through its imports, any proof of the downstream consumers
`UnramifiedTwistedChamberQuotientStatement`,
`UnramifiedTwistedChamberQuotientResidueReductionStatement`,
`UnramifiedTwistedGeneratorChamberStatement`,
`UnramifiedTwistedChamberThroughFixedPointStatement`, `UnramifiedTwistedChamberStatement`,
`LocalSimplyConnectedUnramifiedChamberStatement`,
`LocalSimplyConnectedUnramifiedIntegralTwistStatement`,
`LocalSimplyConnectedUnramifiedCocycleVanishingStatement`,
`LocalSimplyConnectedGaloisCocycleVanishingStatement` and
`LocalSimplyConnectedCocycleVanishingStatement`.
