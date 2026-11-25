# Transporting the solution property to canonical integral closures

Module `StacksFrontier.RingTheory.DiscreteValuationRing.SolutionCanonical`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Let A → B be an extension of discrete valuation rings with fraction fields K → L, and let K₁/K be finite. A solution over K₁ can be presented using abstract integral closures. This file identifies those rings with the chosen subalgebras of K₁ and the reduced tensor product of L and K₁ over K, then transports the solution property.

For an `IntegralClosureBaseChange` package D, `algEquivReducedCompositum` identifies its reduced compositum over B. The maps `algEquivIntegralClosureFractionField` and `algEquivIntegralClosureReducedCompositum` identify its two integral closures over A and B, respectively. `algebraMap_algEquivIntegralClosure` proves compatibility with the map between them.

`isSolution_canonicalBaseChange` turns a solution `hD` on D into a solution on `canonicalBaseChange` for the same finite K₁/K.

Uniqueness of integral closures gives the two equivalences, with compatibility supplied by `D.ringSquare`. For every maximal ideal on the canonical upper ring the proof transports the local arrow using `localizationAtPrimeRingEquivOfRingEquiv` and invariance of maximal-ideal adic formal smoothness under arrow isomorphisms.

The transport keeps the same universe of formal-smoothness test rings.

Tag 09EM and Tag 09EN are the references for the base-change package and solution. Tag 09IL is cited for the application to local rings of a normalized base change.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/DiscreteValuationRing/SolutionCanonical.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
