# Formal smoothness after adjoining a uniformizer root

Module `StacksFrontier.RingTheory.DiscreteValuationRing.Abhyankar.RootUniformizerSmoothness`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

For an extension A → B of discrete valuation rings with fraction fields K → L, the file studies formal smoothness of localized integral closures after finite base change. One case adjoins a root of a uniformizer of A with exponent equal to the ramification index of A → B.

`IsDiscreteValuationRing.formallySmoothNAdic_over_root_uniformizer` takes a uniformizer π of A and n = e(B/A) ≥ 2. Put K₁ = K(π¹⁄ⁿ) and let A₁ be the library’s canonical integral closure in K₁. Given a field quotient E of L ⊗ₖ K₁ and a DVR D obtained by localizing the integral closure of B in E at a prime, it proves that A₁ → D is formally smooth for the maximal-ideal-adic topology. The residue characteristic of A must be zero, or coprime to n with κ(B) separable over κ(A). The compatible DVR extensions, including A → A₁ and A₁ → D, and the irreducibility instance for the defining polynomial are explicit inputs.

`formallySmoothNAdic_tensorProduct_fieldFactor` starts with a finite field extension K₁/K and a surjective L-algebra map L ⊗ₖ K₁ → E compatible with the K₁-map. If A → B is formally smooth for the maximal-ideal-adic topology, the induced map ψ between the localizations of the two integral closures is also formally smooth for the target maximal ideal. The theorem takes as arguments a map g between the closures compatible with K₁ → E, a maximal ideal q of the upper closure with contraction p along g, and ψ from the localization at p to that at q, compatible with g.

In the root case, writing the image of π as a unit times an n-th power yields a formally étale normalization over B, and the root extension has index n and induces an isomorphism on residue fields. For the general field factor the proof applies finite base change to the reduced generic tensor product, then uses the idempotent selecting E to identify the relevant localizations.

`formallySmoothNAdic_of_max_universe` extends testing in the maximum of the two DVR universes to any test-ring universe via `ULift`. `formallySmoothNAdic_of_equiv_square` transports the adic condition along ring equivalences that preserve the defining ideal.

See Tag 0BRM.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/DiscreteValuationRing/Abhyankar/RootUniformizerSmoothness.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 21 declarations of the source file 17 are kept. The 4 left out are not needed by the results for which the extract is made: `IsDiscreteValuationRing.exists_integralClosure_equiv_of_isIntegral`, `IsDiscreteValuationRing.exists_integralClosure_localization`, `IsDiscreteValuationRing.exists_integralClosure_localization_of_isIntegral`, `IsDiscreteValuationRing.isLocalization_comap_of_ringEquiv`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
