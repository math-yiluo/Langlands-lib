# Type R1 coordinates for quasi-split groups

`Langlands.Geometry.Building.quasiSplitR1RootFieldCoordinates` proves
`QuasiSplitR1RootFieldCoordinatesStatement.{u}` for every universe `u`, with exactly
the hypotheses of the published statement.

The implemented proof applies
`quasiSplitR1RootFieldCoordinates_of_structuralStatements` to the four published
theorems `quasiSplitTorusCentralizerExistence`, `maximalSplitTorusConjugacy`,
`rootDatumExistence`, and `relativeRootSystem`. Thus the proof introduces no
additional premise. The reduction shows that the supplied centralizer is a
maximal torus, chooses a finite Galois splitting field, equips the split base
change with its root datum, excludes higher positive root multiples using the
relative root system, and applies `rootFieldCoordinatesOfTorus`.

This is a derived assembly of published Library results. Its mathematical
provenance is the type R1 part of Kaletha–Prasad, *Bruhat–Tits Theory: A New
Approach* (2023), §2.6, especially Notation 2.6.11 and (2.6.1), as documented in
the published statement and reduction. This module proves the R1 coordinate
statement; it does not assert the simple-root transitivity conclusion.
