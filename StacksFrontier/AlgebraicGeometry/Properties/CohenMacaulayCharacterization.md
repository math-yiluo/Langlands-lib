# Stalkwise criteria for Cohen–Macaulay schemes

Module `StacksFrontier.AlgebraicGeometry.Properties.CohenMacaulayCharacterization`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

The Cohen–Macaulay condition for schemes can be checked on local rings, at all points or at closed points only. This file proves these equivalences.

The theorem `isCohenMacaulay_tfae_stalk` equates the scheme condition `IsCohenMacaulay X` with local Noetherianity together with Cohen–Macaulayness of the local rings at all points, or just at closed points.

The proof transports the local condition along the stalk isomorphisms: a private lemma shows that the section ring of a Noetherian affine open is Cohen–Macaulay exactly when all the stalks over that open are, the stalk being a localization of the section ring at a prime. In the closed-point test, every point specializes to a closed point, and Cohen–Macaulayness passes to the further localization at its generization.

The ring and local-ring predicates take explicit Noetherian witnesses in the equivalences. The proof relates the depth-equals-dimension and maximal Cohen–Macaulay forms of the local condition, and transports both along ring isomorphisms.

The module docstring also announces tests on affine opens and open covers, passage to open subschemes, the characterization by Serre’s conditions and the case of normal schemes of dimension at most two; they are not in this file.

References are Stacks Project Tag 02IP and EGA IV 5.7.1.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [02IP](https://stacks.math.columbia.edu/tag/02IP) | `isCohenMacaulay_tfae_stalk` |  |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | IV 5.7.1 | `isCohenMacaulay_tfae_stalk` |  |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Properties/CohenMacaulayCharacterization.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 24 declarations of the source file 9 are kept. The 15 left out are not needed by the results for which the extract is made; `licenses/Stacks/STX-MANIFEST.tsv.md` lists them.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- One reference to EGA or SGA, written in the source as an attribute of that library, is taken out of the Lean text and listed above.
