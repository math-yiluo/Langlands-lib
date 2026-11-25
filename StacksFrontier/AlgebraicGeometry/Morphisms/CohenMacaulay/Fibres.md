# Cohen–Macaulay morphisms and their fibres

Module `StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.Fibres`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

The file relates the pointwise Cohen–Macaulay condition on a morphism to the scheme condition on its fibres.

`isCohenMacaulay_iff_flat_and_fibers` says that `Scheme.Hom.IsCohenMacaulay f hf` holds exactly when f is flat and every scheme-theoretic fibre is Cohen–Macaulay. The definition of the morphism condition takes `hf`, the local Noetherianity of every fibre, as an explicit argument.

The proof uses `Flat.iff_flat_stalkMap` and `isCohenMacaulay_tfae_stalk`. It identifies each point of a fibre with the point `f.asFiber x` coming from its image x in the source.

Tag 045S. EGA IV 19.2.9 gives a more general result.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [045S](https://stacks.math.columbia.edu/tag/045S) | `isCohenMacaulay_iff_flat_and_fibers` |  |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | IV 19.2.9 | `isCohenMacaulay_iff_flat_and_fibers` | more general |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Morphisms/CohenMacaulay/Fibres.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- One reference to EGA or SGA, written in the source as an attribute of that library, is taken out of the Lean text and listed above.
