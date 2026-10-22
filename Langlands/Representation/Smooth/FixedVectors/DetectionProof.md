# Proof of fixed-vector detection and dimension descent

Authors: Worker 1 (assembly and verification) and Worker 196 (the six helper
proofs in `Detection`).

`Langlands.fixedVectorDetectionDescent` proves exactly the published
`Langlands.FixedVectorDetectionDescentStatement.{uR, uG, uV, uW}`. It has no
outer hypotheses or parameters other than the four independent universe
levels. The coefficient field, group, carriers, instances and mathematical
hypotheses remain quantified inside the statement.

The Lean proof constructs the sixfold conjunction in the published order.
After introducing each clause's quantified variables and hypotheses, it
applies, respectively:

1. `Langlands.eq_top_of_fixedVectors_le_of_semisimple`;
2. `Langlands.intertwiner_eq_zero_of_fixedVectorsMap_eq_zero`;
3. `Langlands.SmoothRep.finrank_fixedVectors_kernel_lt`;
4. `Langlands.SmoothRep.finrank_fixedVectors_image_lt`;
5. `Langlands.SmoothRep.finrank_fixedVectors_cokernel_lt`;
6. `Langlands.SmoothRep.not_injective_fixedVectorsMap_of_subquotient_witness`.

The helper module's paired Markdown explains the implemented proofs. In
particular, only the specified fixed spaces are assumed finite dimensional.
The first two clauses are algebraic, the kernel clause allows any topology
and subgroup, and the last three clauses use complex coefficients and a
compact open subgroup of a topological group. The subquotient-witness clause
has no semisimplicity or irreducibility hypothesis.

This is an internal derivation of the published interface from the helper
proofs, not a separate translation of a literature theorem. The helper Lean
file is unchanged from Worker 196's public constituent-induction draft. The
published statement pair and all pairs in its import closure are unchanged.

## Complete declaration and axiom check

The verification uses the project Lean service in environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`). A separate private probe checks the
unapplied theorem, with independently declared universe levels:

```lean
universe uR uG uV uW

example :
    Langlands.FixedVectorDetectionDescentStatement.{uR, uG, uV, uW} :=
  @Langlands.fixedVectorDetectionDescent.{uR, uG, uV, uW}

set_option pp.universes true in
#check @Langlands.fixedVectorDetectionDescent

#print axioms Langlands.fixedVectorDetectionDescent
```

The check succeeded with zero errors and warnings. The printed type is
`Langlands.FixedVectorDetectionDescentStatement.{u_1, u_2, u_3, u_4}` with
four independent universe parameters, and the axiom list is exactly
`[propext, Classical.choice, Quot.sound]`. Declaration inspection likewise
reports the independent parameters `uR`, `uG`, `uV`, `uW` and the same axioms.
The proof-module check and the complete-declaration probe both passed.
Development compilation and this probe do not replace the independent
semantic review or the machine exact-target validation of the submission.
