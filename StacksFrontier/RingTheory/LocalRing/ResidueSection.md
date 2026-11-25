# Compatible coefficient fields in local rings

Module `StacksFrontier.RingTheory.LocalRing.ResidueSection`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

A commutative local ring of prime characteristic with nilpotent maximal ideal admits a coefficient field, given by a ring section of its residue map.

`IsLocalRing.exists_residueField_section_compatible` chooses a section σ for A. For each local ring A′ with a local structure map A → A′, a nilpotent maximal ideal, and a separable residue field extension, it gives a section for A′ that commutes with σ along the map of rings and the induced map of residue fields.

Formal smoothness lifts the identity of each residue field along its residue map, a surjection with nilpotent kernel. The proof first uses separability over the perfect field `ZMod p`. For the second lift, σ gives A′ its κ(A)-algebra structure.

The separability hypothesis uses the library’s predicate `Algebra.StacksIsSeparableExtension`.

The coefficient-field theorem is Tag 09EZ of the Stacks Project.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [09EZ](https://stacks.math.columbia.edu/tag/09EZ) | `exists_residueField_section_compatible` |  |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/LocalRing/ResidueSection.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
