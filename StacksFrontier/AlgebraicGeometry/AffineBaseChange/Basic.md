# Inverse image of a quasi-coherent module along an open immersion

Module `StacksFrontier.AlgebraicGeometry.AffineBaseChange.Basic`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

One lemma on sheaves of modules on schemes.

- `Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback_of_isOpenImmersion`: for an open immersion `f : X ⟶ Y` and a quasi-coherent module `N` on `Y`, the inverse image `f^* N` (`(Scheme.Modules.pullback f).obj N`) is quasi-coherent. The proof transports quasi-coherence of the restriction of `N` along the isomorphism `Scheme.Modules.restrictFunctorIsoPullback f` between restriction and inverse image.

## Watch for

- The module docstring announces local criteria for a morphism of modules to be invertible, a criterion on global sections over an affine scheme, and quasi-coherence of the inverse image along an arbitrary morphism (Tag 01BG), as steps towards Tag 02KG. The file holds none of these, only the open immersion case above.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/AffineBaseChange/Basic.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 7 declarations of the source file 1 are kept. The 6 left out are not needed by the results for which the extract is made: `Stacks.AlgebraicGeometry.AffineBaseChange.isIso_map_of_isIso_app`, `Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_moduleSpecΓ`, `Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_restrict`, `Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_stalk`, `Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback`, `Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback_of_isAffine`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
