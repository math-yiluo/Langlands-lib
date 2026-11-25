# Sections of a module over an affine open via `Spec Γ(X, U)`

Module `StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.AffineSections`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

For an affine open `U` of a scheme `X`, with open immersion `hU.fromSpec : Spec Γ(X, U) ⟶ X`, the global sections of the restriction of a sheaf of modules `F` along `hU.fromSpec` are the sections of `F` over `U`.

- `AlgebraicGeometry.affineSectionsIso F hU`: the isomorphism `Γ(F.restrict hU.fromSpec, ⊤) ≅ Γ(F, U)`, the restriction isomorphism followed by the identification of the image of `Spec Γ(X, U)` with `U`.
- `affineSectionsIso_hom_smul`: this isomorphism commutes with multiplication by elements of `Γ(X, U)`.
- `affineSectionsLinearEquiv F hU`: the same map as a `Γ(X, U)`-linear equivalence, with `affineSectionsLinearEquiv_apply` unfolding it.

## What to watch for

The linearity is a separate lemma: `affineSectionsIso` alone is not stated as linear over `Γ(X, U)`.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Divisors/Meromorphic/AffineSections.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
