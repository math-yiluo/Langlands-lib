# Base change to the spectrum of a stalk

Module `StacksFrontier.AlgebraicGeometry.Pullback.StalkFromSpecStalk`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Base change along the canonical map from the spectrum of the local ring at x to X preserves local rings at points over x.

- `AlgebraicGeometry.flat_fromSpecStalk` proves that the canonical map from the spectrum of the local ring at any point of X is flat.
- `isIso_stalkMap_of_flat_isPreimmersion` shows that a flat preimmersion induces isomorphisms on local rings.
- `exists_point_pullback_fromSpecStalk_isIso_stalkMap` takes any ν : Y ⟶ X and a point y with ν(y) = x. It produces a point of the fibre product above y where the first projection induces a stalk isomorphism.

On an affine neighbourhood the canonical map comes from a localization. After base change it is still a flat preimmersion, so its stalk maps are surjective and faithfully flat, hence isomorphisms. The existence proof pairs y with the closed point of the local spectrum.

The image of the canonical map is described in Stacks Project Tag 01J7.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Pullback/StalkFromSpecStalk.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
