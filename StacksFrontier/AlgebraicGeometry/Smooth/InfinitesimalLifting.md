# Smoothness at a point and formal smoothness of the stalk map

Module `StacksFrontier.AlgebraicGeometry.Smooth.InfinitesimalLifting`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

For a morphism of schemes f : X ⟶ S and a point x of X, the file defines smoothness at x and proves that it makes the induced map of local rings formally smooth.

- `InfinitesimalLifting.SmoothAt f x` means that f is smooth on an open neighbourhood of x: some open U ∋ x has `f.resLE ⊤ U le_top` smooth. It is a neighbourhood condition defined in the file, not a lifting property at x.
- `SmoothAt.formallySmooth_stalkMap` proves that if f is smooth at x, the stalk map 𝒪_{S,f(x)} → 𝒪_{X,x}, with the algebra structure it defines, is formally smooth. No hypothesis beyond smoothness at x is used.

The smooth locus of the smooth restriction is all of U, so its stalk map at x is formally smooth; a private lemma transfers this to f, formal smoothness of the stalk map at a point of U being unchanged by restricting f to U. Schemes are taken in one universe.

The module docstring and the section comments describe the infinitesimal lifting criterion (the equivalence of smoothness at x with lifting properties against square-zero surjections, small extensions and residually trivial small extensions), these two kinds of extension, and the obstruction argument behind Tag 02HT; none of these is in the file. The comments cite Tag 02HX for passing to local rings.

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | IV 17.3.7 | `SmoothAt` |  |
| SGA | 1 II 1.1 | `SmoothAt` |  |
| SGA | 3 VIB 1.3 | `SmoothAt` |  |
| SGA | 3 XI 1.2 | `SmoothAt` |  |
| SGA | 3 XI 1.5 | `SmoothAt` |  |
| SGA | 4 XI 2.1 | `SmoothAt` |  |
| SGA | 7 VI 4.5 | `SmoothAt` |  |
| EGA | 0 19.0.2 | `SmoothAt.formallySmooth_stalkMap` | IV |
| EGA | 0 22.6.4 | `SmoothAt.formallySmooth_stalkMap` | special case |
| EGA | IV 17.5.1 | `SmoothAt.formallySmooth_stalkMap` | a ⇒ c |
| EGA | IV 17.5.3 | `SmoothAt.formallySmooth_stalkMap` | partial |
| EGA | IV 6.8.6 | `SmoothAt.formallySmooth_stalkMap` | a ⇒ c′ |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Smooth/InfinitesimalLifting.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 116 declarations of the source file 3 are kept. The 113 left out are not needed by the results for which the extract is made; `licenses/Stacks/STX-MANIFEST.tsv.md` lists them.
- 25 commands that are not declarations are left out or changed with the declarations left out (`notes/reuse/stacks-extract/extract-commands.tsv.md`).
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 12 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
