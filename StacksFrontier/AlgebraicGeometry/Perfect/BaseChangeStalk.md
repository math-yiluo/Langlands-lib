# Local rings in a base change square

Module `StacksFrontier.AlgebraicGeometry.Perfect.BaseChangeStalk`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

At a point of a fibre product, the local ring is obtained from the local rings
at its three images by tensoring and localizing.

For morphisms X ⟶ Y and Y′ ⟶ Y, let x′ lie in their fibre product. Let A and B
be the local rings at its projections to X and Y′, and R the local ring at
their common image in Y. `BaseChangeStalk.pullback_stalk_isLocalization`
gives a ring map from A ⊗ B over R to the local ring C at x′ that restricts
to the two projection stalk maps. It exhibits C as a localization for the
algebra structure given by this map.

The comparison from the spectrum of the tensor product to the fibre product
is a flat preimmersion, so it induces stalk isomorphisms. Taking the point
corresponding to the inverse image of the maximal ideal of C gives the
desired localization. The proof uses naturality of the canonical maps
from spectra of local rings, with the base actions identified using the
equality of the two images in Y.

The statement supplies a multiplicative submonoid existentially. The proof
takes the complement of the contraction of the maximal ideal of C.

The reference is the Stacks Project chapter *Duality for Schemes*, lemma
“Local rings in the base change square.”

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Perfect/BaseChangeStalk.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 7 declarations of the source file 5 are kept. The 2 left out are not needed by the results for which the extract is made: `AlgebraicGeometry.BaseChangeStalk.pullbackMap_flat_preimmersion_of_comp_mono`, `AlgebraicGeometry.BaseChangeStalk.specMap_stalkMap_congr`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
