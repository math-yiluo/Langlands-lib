# A flat preimmersion is an isomorphism on local rings

Module `StacksFrontier.AlgebraicGeometry.F6Rank89.IdealSheafStalk`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

One result on morphisms of schemes.

- `AlgebraicGeometry.isIso_stalkMap_of_flat_preimmersion`: for a morphism `f : X ⟶ Y` that is flat and a preimmersion (`IsPreimmersion f`), and a point `x` of `X`, the map of local rings `f.stalkMap x : 𝒪_{Y,f x} ⟶ 𝒪_{X,x}` is an isomorphism.

The map is surjective because `f` is a preimmersion (`Scheme.Hom.stalkMap_surjective`), and injective because a flat local homomorphism of local rings is faithfully flat.

## Watch for

- The module docstring announces computations of the stalk of an ideal sheaf (the library's `IdealSheafData.stalk`) and of the ideal sheaf of a reduced closed point, flatness of `X.fromSpecStalk x` and its being a monomorphism, and results on regular schemes. The file holds none of these, only the result above; its namespace `IdealSheafData` is empty.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/F6Rank89/IdealSheafStalk.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 15 declarations of the source file 1 are kept. The 14 left out are not needed by the results for which the extract is made; `licenses/Stacks/STX-MANIFEST.tsv.md` lists them.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
