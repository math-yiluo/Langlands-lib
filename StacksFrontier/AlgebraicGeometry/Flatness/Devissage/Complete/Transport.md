# Fibres under an isomorphism of the source

Module `StacksFrontier.AlgebraicGeometry.Flatness.Devissage.Complete.Transport`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

One construction on morphisms of schemes.

- `AlgebraicGeometry.fiberIsoOfSourceIso e he t`: for morphisms `f : X ⟶ S` and `f' : X' ⟶ S`, an isomorphism `e : X' ≅ X` with `e.hom ≫ f = f'` (`he`) and a point `t` of `S`, an isomorphism of fibres `f'.fiber t ≅ f.fiber t`. It is the canonical map of fibre products with `Spec κ(t)` (`pullback.map` with components `e.hom` and identities), which is invertible because its components are.

## Watch for

- The module docstring announces the transport of the data of a dévissage (one-step dévissages, stages and complete dévissages, pointed or not) along isomorphisms of the source, of the module and of the base, with the comparisons of fibres, supports and dimensions this needs. The file holds none of these, only the isomorphism above; its other sections are empty apart from variable declarations.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Flatness/Devissage/Complete/Transport.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 114 declarations of the source file 1 are kept. The 113 left out are not needed by the results for which the extract is made; `licenses/Stacks/STX-MANIFEST.tsv.md` lists them.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
