# Smoothness from a local model over an affine base

Module `StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.DiscreteValuationStalkAffine`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Over an affine base, a compatible presentation of the source stalk determines the corresponding prime and localized ring on the base.

`smoothAt_of_formallySmoothNAdic_localizationAtPrime_germ` takes a flat, locally finitely presented morphism g : Y ⟶ Spec R and a point y where both stalks are domains and discrete valuation rings. It takes a ring equivalence `φ` from the local ring at y to T_q for an R-algebra T and prime q. The hypothesis `hφ` identifies the germ of the R-structure map with R → T_q. If `hsm` gives formal smoothness of Rₚ → T_q for the maximal-ideal-adic topology of T_q, where p is the contraction of q, then g is smooth at y.

The germ equation identifies p with the prime of g(y). The spectrum stalk isomorphism gives the compatible base localization, so the general DVR stalk criterion applies. This is the affine-base criterion used once the local model is given in the reduced fibre argument.

Stacks Project, Tag 01V9 and Tag 09IL.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Morphisms/Smooth/DiscreteValuationStalkAffine.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
