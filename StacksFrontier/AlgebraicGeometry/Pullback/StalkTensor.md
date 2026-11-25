# Stalks of fibre products over an affine base

Module `StacksFrontier.AlgebraicGeometry.Pullback.StalkTensor`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Let B be an A-algebra, let X be a scheme over Spec A, and let W be its base change to Spec B. A local ring of W is obtained by localizing a tensor product built from a local ring of X.

- `AlgebraicGeometry.specMap_stalkStructureMap` identifies the spectrum map of A → Γ(X, ⊤) → the stalk at x with the canonical map from the local spectrum through X to Spec A.
- `AlgebraicGeometry.exists_isLocalization_atPrime_stalk_tensorProduct` takes w in W and x its image in X. It constructs a map ψ from the tensor product of the stalk at x with B over A to the stalk at w. Its restrictions to the two factors are the first projection’s stalk map and the B-structure map of the stalk at w. It exhibits that stalk as the localization at the contraction along ψ of its maximal ideal.

The tensor product is the ring pushout, so its spectrum is the base change of the local spectrum at x along W ⟶ X. The resulting morphism to W is a flat preimmersion and therefore induces stalk isomorphisms. The map on spectra induced by ψ factors the canonical map from the local spectrum at w through this preimmersion. Comparing at the closed point then gives the asserted localization.

The A-algebra structure on the stalk at x comes from the structure morphism by taking the germ of the map on global sections. The localization prime depends on w. The statement allows arbitrary commutative A-algebras B in the given universe, generalizing the field extension case of Stacks Project Tag 0C4Y.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Pullback/StalkTensor.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
