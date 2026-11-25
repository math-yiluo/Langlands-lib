# Dimension of nonempty opens of an irreducible scheme

Module `StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.NonemptyOpen`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

An irreducible scheme locally of finite type over a field has the same Krull dimension as each of its nonempty opens.

`AlgebraicGeometry.topologicalKrullDim_eq_of_isOpen` takes an explicit locally finite type f : X ⟶ Spec k, an irreducible underlying space, and a nonempty open subset U. It equates the Krull dimensions of X and U with its subspace topology.

On an affine open, the prime-spectrum formula reduces the local dimension to the dimension of the unique irreducible component. Any two nonempty affine opens meet, so comparison at a point in their intersection makes these dimensions equal. Taking suprema of local dimensions gives the comparison for X and U.

This is the nonempty-open clause of Tag 0A21. SGA 3 VIB 1.5 is cited for comparison of the dimensions of opens. The module docstring also announces that the dimension of X is its dimension at every point; the file does not state this.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [0A21](https://stacks.math.columbia.edu/tag/0A21) | `topologicalKrullDim_eq_of_isOpen` | dimension_nonempty_open |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| SGA | 3 VIB 1.5 | `localKrullDim_eq_dim_affineOpen` | partial |
| SGA | 3 VIB 1.5 | `dim_affineOpen_eq_of_nonempty` | special case |
| SGA | 3 VIB 1.5 | `topologicalKrullDim_eq_of_isOpen` | more general |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Variety/Defs/Dimension/NonemptyOpen.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 5 declarations of the source file 4 are kept. The 1 left out are not needed by the results for which the extract is made: `AlgebraicGeometry.topologicalKrullDim_eq_topologicalKrullDimAt_of_irreducible`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 3 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
