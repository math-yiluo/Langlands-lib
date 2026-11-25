# Normality and normalization of a reduced tensor product

Module `StacksFrontier.RingTheory.DiscreteValuationRing.Abhyankar.NormalizationComparison`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Let A → B be an injective local extension of discrete valuation rings with fraction fields K and L, and let K₁/K be finite. The file studies the reduction T of B ⊗ₐ A₁, where A₁ is the integral closure of A in K₁. It compares T with B₁, the integral closure of B in the reduction L₁ of L ⊗ₖ K₁.

- `IsDiscreteValuationRing.ReducedTensorLocalization.actual_normal_ring_reduced_tensor` proves that T is normal when A → B is formally smooth for the maximal-ideal adic topology on B. The local result `actual_every_reduced_maximal_isDVR` gives a discrete valuation ring at each maximal ideal of T.
- `IsDiscreteValuationRing.IntegralClosureComparison.actual_reduced_tensor_normalization_surjective_of_normal` gives an algebra structure on L₁ identifying it with the total ring of fractions of T, and a surjective comparison T → B₁. The comparison respects the maps from B and A₁ and agrees with the fraction-ring map after embedding B₁ in L₁.

For normality, torsion-freeness over the Dedekind domain A₁ gives flatness even after taking the reduction. The special fiber gives a principal maximal ideal in the local ring, and inverting its regular generator gives a field by the criterion for reduced Artinian away localizations. For the comparison, inverting the image of a uniformizer of A in T gives L₁. Its Artinian property makes this localization the total ring of fractions, and integral closedness gives surjectivity.

Both statements use the equivalences `eL₁`, `eA₁` and `eB₁` to specify compatible models. The comparison theorem takes normality as `hNormal`. The first theorem provides it from the adic formal smoothness hypothesis `hformal`.

Stacks Project, Tag 09EQ.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/DiscreteValuationRing/Abhyankar/NormalizationComparison.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
