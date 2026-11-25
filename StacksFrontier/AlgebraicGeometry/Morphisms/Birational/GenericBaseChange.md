# Birational morphisms after generic base change

Module `StacksFrontier.AlgebraicGeometry.Morphisms.Birational.GenericBaseChange`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

A birational morphism becomes an isomorphism after base change to the spectrum of the local ring at a generic point of the target.

`isIso_pullback_snd_fromSpecStalk_of_isBirational` states this for a birational f : X ⟶ Y with finitely many irreducible components in both X and Y. For a generic point y of a component of Y, the projection X ×_Y Spec 𝒪(Y, y) ⟶ Spec 𝒪(Y, y) is an isomorphism. The base change uses the whole local ring, so the conclusion also covers nonreduced generic stalks.

The bijection on generic points supplies the unique generic point x of X over y. The inverse stalk isomorphism gives a section of the projection. All points of the pullback are specializations of the point given by that section, whose image is closed, so the pullback has just one point. Surjectivity on the stalk of the projection and the section then give the isomorphism. The auxiliary result `isIso_stalkMap_fromSpecStalk_closedPoint` identifies the stalk at any x of a scheme with the stalk at the closed point of its local spectrum.

Stacks Project, Tag 0BAB.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [0BAB](https://stacks.math.columbia.edu/tag/0BAB) | `isIso_pullback_snd_fromSpecStalk_of_isBirational` |  |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Morphisms/Birational/GenericBaseChange.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
