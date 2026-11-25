# The canonical integral-closure base change

Module `StacksFrontier.RingTheory.DiscreteValuationRing.IntegralClosureBaseChangeConstruction`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

For an extension A → B of discrete valuation rings with fraction fields K ⊆ L and a finite extension K₁/K, the file constructs the base-change data used in the elimination of ramification.

`reducedCompositum` is the quotient of L ⊗ₖ K₁ by its nilradical. The name refers to the entire reduced tensor product. Write L₁ for this ring, A₁ for the integral closure of A in K₁, and B₁ for the integral closure of B in L₁. The definition `integralClosureCompositumMap` gives A₁ → B₁ by restricting the right-factor map K₁ → L₁.

`canonicalBaseChange` builds the library's `IntegralClosureBaseChange` structure on L₁, A₁ and B₁ with their compatible algebra maps and scalar towers. The theorem `nonempty_integralClosureBaseChange` supplies existence of this package for the given finite extension. The weak and ordinary solution conditions are properties of such packages.

The construction uses `algebraMap_reducedCompositum_eq` to identify the two composites from A to L₁, through B and through K₁. The equality carries integral equations over A to integral equations over B after applying the right-factor map. The resulting map on closures gives the commuting square of the package.

The package places A₁ in the universe of K₁ and L₁ and B₁ in the maximum of the universes of L and K₁. The right tensor-factor algebra structure is installed locally.

References include Tag 09EM for the base-change data and Tag 09EN for the solution conditions.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/DiscreteValuationRing/IntegralClosureBaseChangeConstruction.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
