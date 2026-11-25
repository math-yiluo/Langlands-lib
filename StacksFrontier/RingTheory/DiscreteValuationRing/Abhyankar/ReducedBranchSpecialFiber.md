# Special fibres of reduced tensor branches

Module `StacksFrontier.RingTheory.DiscreteValuationRing.Abhyankar.ReducedBranchSpecialFiber`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

In the discrete valuation ring extension A → B with fraction fields K → L, take a finite extension K₁ of K. Let A₁ model the integral closure of A in K₁ and B₁ the integral closure of B in the reduction of L ⊗ₖ K₁. The file studies the local rings of the reduced tensor product of B and A₁ at primes selected by maximal ideals of B₁.

`ReducedTensorLocalization.actual_09EM_reduced_branch_specialFiber_isField` uses compatible identifications of these models, a maximal ideal q of B₁ and adic formal smoothness `hformal` of A → B for the maximal ideal of B. It constructs an integral map g from the tensor product B ⊗ A₁ over A to B₁ whose kernel consists of nilpotents and whose restrictions are the given maps. The contraction m of q to A₁ is maximal and the localization of A₁ at m is a DVR. At the prime of the reduced tensor product corresponding to the contraction along g, the fibre over m is a field. There is a compatible algebra map from the localized A₁, and the image of a uniformizer generates the maximal ideal of the reduced local ring.

`local_extension_equivalentClosure` gives a local DVR extension of A at any maximal ideal of a Dedekind model of an integral closure in a finite field extension. `selected_branch_away_artinian_of_base_extension` shows that inverting the image of the chosen local uniformizer yields a reduced Artinian ring. It assumes a local DVR extension, compatibility of the local map with the right tensor factor, and an identification of the raw generic localization with a tensor product of fields with the right field finite over the common base.

The special-fibre proof uses the integral-closure comparison after finite extension and the weak unramifiedness and residue separability supplied by adic formal smoothness. Localization commutes with reduction, and the field quotient survives reduction because its maximal ideal contains the nilradical.

The principal maximal ideal statement identifies the image of a uniformizer from the localized A₁. Its conclusion concerns this selected reduced branch and retains the explicit compatibility conditions on the ring and field maps.

See Tag 09EQ.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/DiscreteValuationRing/Abhyankar/ReducedBranchSpecialFiber.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
