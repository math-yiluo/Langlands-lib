# Birational morphisms and generic stalks

Module `StacksFrontier.AlgebraicGeometry.Morphisms.Birational.Basic`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Birationality of a morphism is expressed by its action on the generic points of irreducible components and on the local rings at those points.

`IsBirational f` requires a bijection from the generic points of the source to those of the target and an isomorphism on the stalk at each generic point of the source. The projections `IsBirational.bijOn` and `IsBirational.isIso_stalkMap` recover the two conditions, and `isBirational_of_bijOn_of_isIso_stalkMap` constructs the predicate from them. The module docstring also lists an `iff` form of the definition, which the file does not contain.

The definition applies to arbitrary schemes, extending the finite-component setting of Tag 01RO. It uses isomorphisms of local rings, so the generic-point condition includes the stalk structure on nonreduced schemes.

See EGA I 2.2.9, EGA I 6.5.5 and EGA IV 6.15.4.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [01RO](https://stacks.math.columbia.edu/tag/01RO) | `IsBirational` |  |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | I 2.2.9 | `IsBirational` |  |
| EGA | IV 6.15.4 | `IsBirational` | finitely many comps |
| EGA | I 6.5.5 | `IsBirational` |  |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Morphisms/Birational/Basic.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 5 declarations of the source file 4 are kept. The 1 left out are not needed by the results for which the extract is made: `AlgebraicGeometry.isBirational_iff`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 3 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
