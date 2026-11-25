# The residue-field action on the local ring of a fibre

Module `StacksFrontier.AlgebraicGeometry.SmoothAtClosedFibre.Basic`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

This file describes the local ring of the scheme-theoretic fibre at the point determined by x for a morphism f from X to S. It identifies its residue-field algebra structure and relates it to smoothness of the fibre.

`Stacks.SmoothAtClosedFibre.kappaToFibreStalk` is the ring map from κ(f(x)) to that local ring, defined via the stalk map of the fibre's structure morphism over the spectrum of κ(f(x)). `residueFieldToFibreStalkIso` identifies the field with the stalk of its spectrum at the image of the fibre point. `arrowIso_kappaToFibreStalk` packages the resulting comparison of the two ring maps.

`stalkClosedPointTo_fromSpecResidueField` identifies the local map of the canonical residue-field point with the residue map. `residue_kappaToFibreStalk` then shows that precomposing the fibre's field action with residue gives the same map as composing the stalk map of f with that of the fibre inclusion, with the point identifications inserted.

`formallySmooth_kappaToFibreStalk` assumes f locally of finite presentation and the fibre smooth at its point over κ(f(x)). It concludes that the field-to-stalk map is formally smooth. The proof uses the smooth-locus characterization on the fibre and transports formal smoothness along the arrow isomorphism.

This last implication treats the smooth-fibre conjunct of condition (2) of Tag 01V9. The file also cites Tag 00TF.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/SmoothAtClosedFibre/Basic.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 10 declarations of the source file 9 are kept. The 1 left out are not needed by the results for which the extract is made: `Stacks.SmoothAtClosedFibre.stalkCongr_inv_of_eq`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
