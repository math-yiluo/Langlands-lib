# Proof of `Langlands.GroupScheme.ParabolicIntersectionSplitTorusStatement`

This module proves the published proposition `Langlands.GroupScheme.ParabolicIntersectionSplitTorusStatement` (module `Langlands.GroupScheme.Rational.ParabolicIntersectionAssembly`) at every universe `u`. The statement says that for a connected reductive group over a field and two parabolic subgroups `j`, `j'`, some maximal split torus factors through both.

The theorem is `Langlands.GroupScheme.parabolicIntersectionSplitTorus : ParabolicIntersectionSplitTorusStatement.{u}`, with no hypotheses.

## Proof

The proof term is the published reduction `parabolicIntersectionSplitTorusStatement_of_centralizer`, which derives it from the centralizer form `ParabolicIntersectionCentralizerStatement`, applied to the published proof `parabolicIntersectionCentralizer` of that form.

The theorem adds no mathematics; it names a combination of published results.

## Published inputs

- `Langlands.GroupScheme.parabolicIntersectionSplitTorusStatement_of_centralizer` (module `Langlands.GroupScheme.Rational.ParabolicIntersectionAssembly`)
- `Langlands.GroupScheme.parabolicIntersectionCentralizer` (module `Langlands.GroupScheme.Rational.ParabolicIntersectionCentralizerProof`)
