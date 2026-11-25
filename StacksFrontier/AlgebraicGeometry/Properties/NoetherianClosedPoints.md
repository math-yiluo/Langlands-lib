# Closed points on locally Noetherian schemes

Module `StacksFrontier.AlgebraicGeometry.Properties.NoetherianClosedPoints`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Local Noetherianity ensures that the closure of any point contains a point closed in the ambient scheme. The file gives three forms of this assertion.

- `AlgebraicGeometry.closedPoints_nonempty` proves that a nonempty locally Noetherian scheme X has a closed point.
- `AlgebraicGeometry.nonempty_inter_closedPoints_of_isClosed` proves that every nonempty closed subset Z of a locally Noetherian X contains a point closed in X.
- `AlgebraicGeometry.exists_specializes_closedPoint` proves that each point x of a locally Noetherian X specializes to some closed point y.

For existence, choose a point closed in a nonempty affine open, then give its closure the reduced induced scheme structure. In this integral locally Noetherian subscheme, the chosen point is an open singleton. A private dimension lemma shows that the local ring at any specialization of an open singleton in an integral locally Noetherian scheme has dimension less than two. The singleton pulls back to an open singleton in the spectrum of the local ring, whereas in dimension at least two every nonempty open of that spectrum is infinite. A chain of two strict specializations would give a local ring of dimension at least two. Thus the chosen point or a strict specialization of it is closed in X.

The closed-subset version applies existence to the reduced induced subscheme of Z and uses its closed embedding. The specialization version takes Z to be the closure of x.

References are Stacks Project Tag 02IL and EGA IV 5.1.11.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [02IL](https://stacks.math.columbia.edu/tag/02IL) | `closedPoints_nonempty` | nonempty scheme |
| [02IL](https://stacks.math.columbia.edu/tag/02IL) | `nonempty_inter_closedPoints_of_isClosed` | nonempty closed subset |
| [02IL](https://stacks.math.columbia.edu/tag/02IL) | `exists_specializes_closedPoint` | closed specialization |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | IV 5.1.11 | `nonempty_inter_closedPoints_of_isClosed` |  |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Properties/NoetherianClosedPoints.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- One reference to EGA or SGA, written in the source as an attribute of that library, is taken out of the Lean text and listed above.
