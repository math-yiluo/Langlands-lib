# Stalks of the adjunction-defined module pullback

Module `StacksFrontier.Topology.Sheaves.RingedSpace.ModulePullbackStalkAdjunction`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

For a morphism f of ringed spaces from X to Y, the stalk at x of the pullback of a sheaf of modules G is the extension of scalars of the stalk of G at f(x) along the induced map on structure stalks. The equivalence is characterized by what it does to germs of sections mapped by the adjunction unit.

`exists_modulePullbackStalkLinearEquiv` gives a linear equivalence from the stalk of `modulePullback` to the tensor product of the structure stalk at x with the stalk of G at f(x), over the structure stalk at f(x). For every open V containing f(x) and section s over V, the equivalence sends the germ at x of the unit image of s over f⁻¹V to 1 tensored with the germ of s at f(x).

`moduleStalkMap` defines the linear map on stalks induced by a module presheaf morphism, and `moduleStalkMap_germ` shows that it sends the germ of a section to the germ of its image. The hom-set equivalence `moduleStalkSkyscraperHomEquiv` identifies linear maps from a module stalk to a module N over the structure stalk with morphisms into the skyscraper presheaf with value N. Its two directions use the germ maps and the identification of the skyscraper stalk with N, respectively.

The proof compares maps out of the presheaf pullback stalk with maps out of the tensor product by using the stalk–skyscraper, pullback–pushforward, and extension–restriction of scalars correspondences. Pushing a skyscraper forward moves its point to f(x) and restricts its scalars. Testing maps into all modules makes the canonical tensor-to-stalk map invertible, and the comparison with sheafification transports the equivalence and its formula on unit germs.

The private reduction `exists_modulePullbackStalkLinearEquiv_of_bridge` takes `h : PresheafPullbackStalkBridge f G x`, the unit-compatible stalk formula for presheaf pullback, which the public theorem establishes internally. The theorem uses the adjunction-defined pullback, with the structure stalk acting on the left tensor factor. Spaces, rings, and module sections live in one universe.

Reference is Stacks Project Tag 0098.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [0098](https://stacks.math.columbia.edu/tag/0098) | `exists_modulePullbackStalkLinearEquiv` |  |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/Topology/Sheaves/RingedSpace/ModulePullbackStalkAdjunction.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
