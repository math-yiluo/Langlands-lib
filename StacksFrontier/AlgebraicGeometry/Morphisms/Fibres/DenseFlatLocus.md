# Generic flatness for a morphism and a closed subscheme

Module `StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.DenseFlatLocus`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Over a reduced base, a finite type morphism becomes flat and finitely presented over a dense open. The file also applies this to the reduced closed subscheme associated with a closed subset of the source.

`AlgebraicGeometry.exists_dense_open_flat_finitePresentation_structureSheaf` takes f with reduced target and instances `LocallyOfFiniteType f` and `QuasiCompact f`. It gives a dense open U on which the restriction of f is flat and of finite presentation. It applies generic flatness to the structure sheaf, which is quasi-coherent and of finite type as a module over itself.

Under the same hypotheses, `exists_dense_opens_flat_source_and_closed` takes a closed set Z in the source. It applies the first result to f and to the composite from the subscheme cut out by the vanishing ideal of Z. The statement supplies two dense opens of the base, one for each morphism.

Stacks Project, Tag 052B for generic flatness.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Morphisms/Fibres/DenseFlatLocus.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
