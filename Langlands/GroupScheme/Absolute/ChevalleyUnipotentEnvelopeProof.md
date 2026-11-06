# The unipotent envelope in the Borel subgroups through a maximal torus

This module proves
`Langlands.GroupScheme.ChevalleyUnipotentEnvelopeStatement.{u}` as the
theorem `Langlands.GroupScheme.chevalleyUnipotentEnvelope`, at an arbitrary
universe `u`.

The statement is as follows. Let `k` be an algebraically closed field and `G`
a smooth connected affine group scheme over `Spec k`. Let `t : T ⟶ G` be a
maximal torus. Let `i : U ⟶ G` be a smooth connected unipotent closed
subgroup that lies in every Borel subgroup of `G` containing `T`. Then `U`
lies in a smooth connected unipotent closed subgroup `n : N ⟶ G` whose range
is normal in `G`. Containment of subgroups means containment of the subgroup
functors `SubgroupFunctor.range`, that is, on points over every test scheme.

## Proof

The proof uses two published theorems. Both are proofs of statements in
`Langlands.GroupScheme.Absolute.ChevalleyUnipotentEnvelopeSteps`.

1. The flag step `unipotentTorusBorelsToAllBorels`, from module
   `Langlands.GroupScheme.Absolute.UnipotentTorusBorelsToAllBorelsProof`,
   proves `UnipotentTorusBorelsToAllBorelsStatement.{u}`. Given the data
   above, it shows that `U` lies in every Borel subgroup of `G`.
2. The envelope step `unipotentAllBorelsEnvelope`, from module
   `Langlands.GroupScheme.Absolute.UnipotentAllBorelsEnvelopeProof`,
   proves `UnipotentAllBorelsEnvelopeStatement.{u}`. If a smooth connected
   unipotent closed subgroup lies in every Borel subgroup, this step gives a
   smooth connected unipotent closed subgroup `n : N ⟶ G` with normal range
   that contains it.

The Lean proof introduces all the data and hypotheses of the target. It
applies the flag step to `G`, `T`, `t`, the maximal-torus hypothesis, `U`,
`i`, the hypotheses on `U`, and the hypothesis about the Borel subgroups
through `T`. This shows that `U` lies in every Borel subgroup. It then
applies the envelope step to `G`, `U`, `i`, the same hypotheses on `U`, and
that conclusion. The conclusion of the envelope step is the conclusion of
the target, with the same predicates, so no conversion is needed.

## Provenance

The theorem is the unipotent-envelope consequence of J. S. Milne,
*Algebraic Groups* (2017), Theorem 17.56. The split into the two steps
follows Luna's proof of that theorem in Section 17.h (printed pp.373–375).
The Markdown files of the two proof modules describe how each step is
proved in Lean.
