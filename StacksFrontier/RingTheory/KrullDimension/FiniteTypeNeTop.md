# Finite Krull dimension over a field

Module `StacksFrontier.RingTheory.KrullDimension.FiniteTypeNeTop`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

A finitely generated commutative algebra over a field has bounded Krull dimension.

`stacks_ringKrullDim_ne_top_of_finiteType` shows that `ringKrullDim A ≠ ⊤` for a field κ and an algebra A of finite type over κ. A presentation as a quotient of a polynomial ring in finitely many variables bounds the dimension by the number of variables. The conclusion also permits the bottom value, which is the dimension of the zero algebra. The module docstring lists the theorem under its name without the `stacks_` prefix.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/KrullDimension/FiniteTypeNeTop.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- Renamed, the source's name being declared elsewhere as well (`licenses/Stacks/STX-RENAMES.tsv.md`): `ringKrullDim_ne_top_of_finiteType` is `stacks_ringKrullDim_ne_top_of_finiteType` here.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
