# The minimum defining the level of a degree-p extension

Module `StacksFrontier.RingTheory.DiscreteValuationRing.ExtensionLevel.LevelDefinition`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

The file defines the level used for cyclotomic quotient presentations of extensions of discrete valuation fields.

- `IsDegreePExtensionOfFiniteLevel` asks for degree p and a generator z satisfying P(z) = ξ, with wᵖξ in the maximal ideal of the base ring, where w is one minus the image of the cyclotomic root.
- `extensionLevelNumerators` collects natural numbers n for which πⁿξ comes from the base ring for some generating equation P(z) = ξ, with π supplied. `extensionLevel` takes a proof that this set is nonempty and divides its infimum by a supplied positive integer e₁.
- `exists_extensionLevel_isLeast_and_mem_Ico` assumes finite level, a uniformizer π, and w associated to π raised to e₁. The minimum is attained and its normalized value is in [0, p).

The maximal-ideal condition supplies the candidate pe₁ − 1. Taking the least candidate uses well-ordering of the natural numbers.

The predicate takes the polynomial and cyclotomic map as inputs and puts the ring and fields in one universe. The minimum theorem allows independent universes by expressing its finite-level premise `hfinite` on `ULift` copies.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/DiscreteValuationRing/ExtensionLevel/LevelDefinition.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
