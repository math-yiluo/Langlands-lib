# Discrete valuation rings at codimension one

Module `StacksFrontier.AlgebraicGeometry.Properties.NormalStalkDvr`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

On a locally Noetherian normal scheme, the stalk at a codimension-one point is a discrete valuation ring.

`AlgebraicGeometry.isDiscreteValuationRing_stalk_of_coheight_eq_one` assumes `IsLocallyNoetherian X`, `IsNormal X` and `Order.coheight x = 1`. It concludes `IsDiscreteValuationRing (X.presheaf.stalk x)`.

The proof identifies the stalk’s Krull dimension with the coheight of x, then applies `isDiscreteValuationRing_tfae` to the resulting one-dimensional Noetherian local integrally closed domain.

The domain condition is on the stalk and follows from the scheme’s normality, so the theorem also applies to reducible normal schemes.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Properties/NormalStalkDvr.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
