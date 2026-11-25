# Generic and special fibres of tensor branches

Module `StacksFrontier.RingTheory.DiscreteValuationRing.Abhyankar.TensorSpecialFiber`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

This file develops local calculations for tensor products in the proof of Abhyankar’s lemma. It gives conditions for a branch to have a field as its special fibre and for the generic localization of a reduced branch to be Artinian.

`ReducedTensorLocalization.weaklyUnramified_and_separable_of_formallySmooth` applies to an extension A → B of DVRs that is formally smooth for the maximal-ideal-adic topology on B. It shows that the maximal ideal of A extends to the maximal ideal of B and that κ(B) is separable over κ(A) in the sense of `Algebra.StacksIsSeparableExtension`.

`selected_global_tensor_specialFiber_isField` starts with local maps A → B and A → D, where D is the localization of an A-algebra C at p. If the maximal ideal of A extends to that of B, κ(B)/κ(A) is separable, and κ(D)/κ(A) is finite, then the local ring of B ⊗ C over A at any prime r lying over p has a field quotient by the extension of p.

`selected_branch_away_artinian_reduced_of_generic_equiv` assumes that inverting the image of πₐ in B ⊗ D over A gives a ring isomorphic to L ⊗ E over K, where L and E are field extensions of K and E is finite over K. Let q be a prime of the reduction of the original tensor product. If the image of πₐ in the local ring at q is associated to a positive power of π, inverting π there gives a reduced Artinian ring.

For the special fibre, the proof localizes the right tensor factor and computes the fibre as a tensor product of residue fields, which is reduced and Artinian. For the generic statement, finiteness gives Artinianness and the relation between parameters gives equivalent localizations.

The special-fibre criterion uses weak unramifiedness and residue separability directly. The generic statement takes the comparison isomorphism and the association of parameters as hypotheses, and its reducedness conclusion is for the localization of the reduced tensor product.

See Tag 09EQ for the formal-smoothness base-change setting.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/DiscreteValuationRing/Abhyankar/TensorSpecialFiber.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
