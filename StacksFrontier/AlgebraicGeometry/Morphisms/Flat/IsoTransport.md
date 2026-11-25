# Relative flatness under module isomorphism

Module `StacksFrontier.AlgebraicGeometry.Morphisms.Flat.IsoTransport`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

For a morphism of ringed spaces p : X ⟶ Y, relative flatness of a sheaf of modules is flatness of its stalk at x over the base stalk at p(x). This property is invariant under isomorphism of sheaves of modules on X.

Given an isomorphism F ≅ G and a point x, `isFlatOverAt_of_moduleIso` transfers flatness over Y at x from F to G. `isFlatOverAt_iff_of_moduleIso` gives the pointwise equivalence. The global form that the module docstring also lists is not in the file.

The induced linear equivalence on stalks is linear over the base by restriction of scalars. The proof checks on germs that `SemilinearStalk.commStalkRingEquiv` identifies the actions calculated in `RingCat` and `CommRingCat`.

The space, ring and module universes agree in these statements. For schemes, apply the lemmas to the underlying ringed-space morphism.

Reference is Stacks Project Tag 08KT.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Morphisms/Flat/IsoTransport.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 5 declarations of the source file 4 are kept. The 1 left out are not needed by the results for which the extract is made: `AlgebraicGeometry.isFlatOver_iff_of_moduleIso`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
