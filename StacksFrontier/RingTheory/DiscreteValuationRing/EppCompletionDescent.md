# Descent of a weak solution across a completion square

Module `StacksFrontier.RingTheory.DiscreteValuationRing.EppCompletionDescent`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Consider a commutative square of extensions of discrete valuation rings with horizontal maps A → Ac and B → Bc and vertical maps A → B and Ac → Bc. The intended horizontal maps are completions. The file transports weak solutions through this square.

- `isWeakSolution_of_isWeakSolution_completion` takes finite extensions K₁/K and M/Kc of the fraction fields of A and Ac. If K₁ supplies a weak solution for A → Ac and M supplies one for Ac → Bc, it gives a weak solution for A → B along K₁, provided the reduced compositum for A → Ac is Kc-isomorphic to M.
- `isWeakSolution_of_isWeakSolution_completion_of_tensorProduct_algEquiv` takes the equivalence `e` directly on Kc ⊗[K] K₁. A helper transfers it to the reduced compositum in the supplied data because an algebra isomorphic to a field has zero nilradical.

The proof composes the two weak solutions along A → Ac → Bc using the one-factor product with factor M, then descends along A → B → Bc using Tag 09ES.

The statement works with an abstract square, even without completeness. It takes four `IntegralClosureBaseChange` packages as input, `D_AB`, `D_AAc`, `D_ABc` and `D_AcBc`. The hypothesis `hAAc` supplies the weak solution along A → Ac, and the compositum equivalence is also an input. In the completion application, these come from the results cited as Tag 09E7, Tag 09EQ, Tag 09EM and Tag 09EJ. The carriers and the presentation universes of the packages are independent.

This is the transport part of step 3 of Tag 09F9.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/DiscreteValuationRing/EppCompletionDescent.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
