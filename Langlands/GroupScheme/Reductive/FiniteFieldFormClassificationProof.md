# Classification of forms of a split reductive group over a finite field

Authors: Worker 148 and Worker 187.

`finiteFieldFormClassification` proves the unchanged
`Langlands.GroupScheme.FiniteFieldFormClassificationStatement.{u}` in every universe, with
no additional hypotheses.

The proof applies the published reduction
`finiteFieldFormClassification_of_innerFormStarAction`
(`Langlands/GroupScheme/Reductive/FiniteFieldFormClassificationReduction.lean`) to two
published proofs:

- `innerFormStarAction : InnerFormStarActionStatement.{u}`
  (`InnerFormStarActionProof.lean`, Task 6546). Inner forms of a
  reductive group are detected by the star action. The reduction uses it in both
  directions of clause 2.
- `finiteFieldFormExistence : FiniteFieldFormExistenceStatement.{u}`
  (`FiniteFieldFormExistenceProof.lean`). This is clause 1: every finite-order based
  automorphism is the Frobenius class of a form, built by `SplitPinning.finiteFieldForm`.

Clause 2 is proved in the reduction module. An isomorphism `G ≅ G'` gives an inner
discrepancy over `k`, so inner-form detection yields a base-preserving root-datum
equivalence that intertwines the star actions; at the Frobenius, this makes the two classes
conjugate. Conversely, a conjugating based automorphism gives an equivalence that
intertwines the Frobenius star actions. It therefore intertwines every star action,
because each Galois element acts on a finite stage as a power of the Frobenius. Inner-form
detection then gives an inner form over a finite Galois extension. Its inner cocycle with
values in the adjoint quotient is trivial by Lang's theorem (`Cocycle.isTrivial_of_finite`),
so the isomorphism descends to `k`.

This follows Conrad, *Reductive group schemes* (2014), Proposition 7.2.2, the remark on
Lang's theorem, and Example 7.2.3 (printed p.252).
