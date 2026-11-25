# Flatness on ringed spaces

Module `StacksFrontier.AlgebraicGeometry.RingedSpace.Flat`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Flatness of a morphism of ringed spaces at a point and relative flatness of a sheaf of modules are defined stalkwise.

For f : X ⟶ Y, `AlgebraicGeometry.IsFlatAt` applies Mathlib's `RingHom.Flat` to the map from the stalk at f(x) to the stalk at x.

For an 𝒪ₓ-module F, `AlgebraicGeometry.IsFlatOverAt` requires the stalk of F at x to be flat over the stalk of 𝒪ᵧ at f(x). The module structure is obtained by restricting scalars along the stalk map using `Module.compHom`. `AlgebraicGeometry.IsFlatOver` requires this at every source point.

The definition of flatness at a point is from Tag 02N3 and those of module flatness from Tag 08KT. See also EGA 0 6.7.1. The module docstring also lists a predicate for a morphism flat at every point, which the file does not contain.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [02N3](https://stacks.math.columbia.edu/tag/02N3) | `IsFlatAt` | flat at a point |
| [08KT](https://stacks.math.columbia.edu/tag/08KT) | `IsFlatOverAt` | part (1) |
| [08KT](https://stacks.math.columbia.edu/tag/08KT) | `IsFlatOver` | part (2) |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | 0 6.7.1 | `IsFlatAt` | f flat at x |
| EGA | 0 6.7.1 | `IsFlatOverAt` | F f-flat at x |
| EGA | 0 6.7.1 | `IsFlatOver` | F f-flat (all x) |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/RingedSpace/Flat.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 4 declarations of the source file 3 are kept. The 1 left out are not needed by the results for which the extract is made: `AlgebraicGeometry.IsFlat`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 3 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
