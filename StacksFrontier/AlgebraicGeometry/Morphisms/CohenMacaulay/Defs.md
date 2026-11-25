# Cohen–Macaulay morphisms

Module `StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.Defs`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Cohen–Macaulayness of a scheme morphism combines flatness at a source point with Cohen–Macaulayness of the local ring of the fibre at that point.

`Scheme.Hom.IsCohenMacaulayAt f hf x` requires flatness at x and `IsCohenMacaulayLocalRing` for the stalk at the point of the scheme-theoretic fibre over f(x) corresponding to x. `Scheme.Hom.IsCohenMacaulay f hf` requires this at every source point. Both are predicates with `hf` supplying local Noetherianity of every fibre.

`isLocallyNoetherian_fiber_of_locallyOfFinitePresentation` supplies that hypothesis for a locally finitely presented morphism. After base change to the spectrum of the residue field, local finite type over the field gives local Noetherianity. The file also defines the canonical fibre isomorphism over equal base points and its compatibility with the inclusions.

See Tag 045R, parts (1) and (2), EGA IV 6.8.1(ii) and SGA 1 II 4.19.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [045R](https://stacks.math.columbia.edu/tag/045R) | `IsCohenMacaulayAt` | part (1) |
| [045R](https://stacks.math.columbia.edu/tag/045R) | `IsCohenMacaulay` | part (2) |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | IV 6.8.1 | `IsCohenMacaulayAt` | (ii) |
| SGA | 1 II 4.19 | `IsCohenMacaulayAt` |  |
| EGA | IV 6.8.1 | `IsCohenMacaulay` | (ii), global |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Morphisms/CohenMacaulay/Defs.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 3 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
