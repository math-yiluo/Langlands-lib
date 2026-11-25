# Integral closure and localization of reduced fraction rings

Module `StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.StalkIntegralClosureLocalization`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

The file compares integral closures under localization and under passage through an integral intermediate ring.

`integralClosure_eq_restrictScalars_of_isIntegral` says that in a compatible tower R → A → B with A integral over R, the integral closures of R and A in B agree as R-subalgebras. It uses ascent and transitivity of integrality.

`nonempty_algEquiv_integralClosure_fractionRing_reduction` takes a localization C of R at M and assumes the total fraction ring S of the reduction of R is Artinian. The integral closure of C in the total fraction ring of its reduction is isomorphic over C to the localization of the integral closure of R in S at the image of M.

The proof localizes the integral closure and transports it along the comparison of the reduced total fraction rings. The conclusion is existence of a C-algebra equivalence, with the localization's C-algebra structure given by `localizationAlgebra`.

Stacks Project, Tag 0C3B.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Morphisms/Normalization/StalkIntegralClosureLocalization.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
