# Irreducible components of quasi-compact opens of locally Noetherian schemes

Module `StacksFrontier.AlgebraicGeometry.Properties.Noetherian`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

A quasi-compact open of a locally Noetherian scheme has finitely many irreducible components.

`AlgebraicGeometry.finite_irreducibleComponents_of_isCompact` takes a locally Noetherian scheme X and an open U of X that is quasi-compact, and shows that U has finitely many irreducible components.

As a scheme, U is locally Noetherian and compact, hence Noetherian, so its underlying Noetherian space has finitely many components.

The module docstring also announces that the space underlying a locally Noetherian scheme is locally Noetherian, the local half of Stacks Project Tag 01OZ; that result is not in this file.

The component finiteness result is recorded as a special case of EGA 0 2.2.5, EGA I 7.3.3 and EGA IV 2.3.6.

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | 0 2.2.5 | `finite_irreducibleComponents_of_isCompact` | special case |
| EGA | I 7.3.3 | `finite_irreducibleComponents_of_isCompact` | special case |
| EGA | IV 2.3.6 | `finite_irreducibleComponents_of_isCompact` | special case |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Properties/Noetherian.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 2 declarations of the source file 1 are kept. The 1 left out are not needed by the results for which the extract is made: `AlgebraicGeometry.isLocallyNoetherianSpace_of_isLocallyNoetherian`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 3 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
