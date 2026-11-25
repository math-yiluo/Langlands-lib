# Local presentations and quasi-coherence of modules on schemes

Module `StacksFrontier.AlgebraicGeometry.AffinePushforward.Basic`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Two facts about presentations of modules on a scheme, with the constructions behind them: quasi-coherence is local, and on a scheme isomorphic to a spectrum a quasi-coherent module has a global presentation.

## Results

- `isQuasicoherent_of_presentations`: a module `M` on `X` whose restrictions `M.restrict (U i).ι` to the members of an open cover `U : I → X.Opens` (`IsOpenCover U`) all have presentations is quasi-coherent. It is the quasi-coherence of `quasicoherentDataOfPresentations`, Mathlib's `QuasicoherentData` built from these presentations.
- `presentationOver`: a presentation of `M.restrict V.ι` gives one of `M.over V`, the form `QuasicoherentData` asks for. It is transported along the inverse of the equivalence `Scheme.Modules.overEquiv V`, with `overInverseIso` and `overInverseUnitIso` identifying `M.over V` and the structure sheaf with their images under that inverse, and the instance `isLeftAdjointOverEquivInverse` making the inverse a left adjoint.
- `presentationOfIso`: a presentation of a sheaf of modules on a site, transported along an isomorphism `M ≅ N`.
- `nonempty_presentation_of_isoSpec`: for `e : Y ≅ Spec R` and a quasi-coherent module `N` on `Y`, `N` has a global presentation.

## Proof

For `nonempty_presentation_of_isoSpec`, the restriction of `N` along `e.inv` is quasi-coherent, so its comparison map `fromTildeΓ` is invertible (`isQuasicoherent_iff_isIso_fromTildeΓ`) and `presentationTilde` presents it; that presentation is restricted back along `e.hom` and transported to `N`.

## Watch for

- The index type `I` of the cover in `isQuasicoherent_of_presentations` lies in the universe `u` of the scheme.
- The module docstring announces that the direct image of a quasi-coherent module along an affine morphism is quasi-coherent (the first assertion of Tag 02KG), together with a base-change isomorphism for restriction to an open of the base and the affine case. The file holds none of these; its sections on them are empty.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/AffinePushforward/Basic.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 15 declarations of the source file 8 are kept. The 7 left out are not needed by the results for which the extract is made: `Stacks.AlgebraicGeometry.AffinePushforward.isQuasicoherent_of_iso`, `Stacks.AlgebraicGeometry.AffinePushforward.isQuasicoherent_pushforward_of_isAffine`, `Stacks.AlgebraicGeometry.AffinePushforward.isQuasicoherent_pushforward_of_isIso`, `Stacks.AlgebraicGeometry.AffinePushforward.isQuasicoherent_pushforward_specMap`, `Stacks.AlgebraicGeometry.AffinePushforward.opensFunctorRestrictIso`, `Stacks.AlgebraicGeometry.AffinePushforward.pushforward_isQuasicoherent_of_isAffineHom`, `Stacks.AlgebraicGeometry.AffinePushforward.restrictPushforwardIso`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
