# Lifting homomorphisms from groups of multiplicative type over complete local rings

`Langlands.GroupScheme.multiplicativeTypeCompleteLocalLift` proves the unchanged
[`MultiplicativeTypeCompleteLocalLiftStatement.{u}`](MultiplicativeTypeCompleteLocalLiftStatement.md)
in every universe, with no extra hypotheses. Let `A` be a complete local noetherian ring
with residue field `k`, let `H` be of multiplicative type over `Spec A`, and let `G` be
smooth affine over `Spec A`. Every homomorphism `H_k ⟶ G_k` lifts to `H ⟶ G`.
Two lifts of the same homomorphism are conjugate by a point of `G(Spec A)` reducing to
`1` in `G(k)`. A homomorphism whose special fibre is a closed immersion is itself a
closed immersion.

## Implemented proof

The proof applies [`multiplicativeTypeCompleteLocalLift_of_adicLift`](MultiplicativeTypeCompleteLocalLiftReduction.md)
to the published [`multiplicativeTypeAdicLift`](MultiplicativeTypeAdicLiftProof.md).
The reduction uses completeness to obtain a Henselian local ring. The Henselian clause
of `multiplicativeTypeQuasiIsotrivial` then supplies a finite étale surjective cover
on which `H` becomes diagonalizable. The adic lifting theorem at the maximal ideal of
`A` gives existence and conjugacy of lifts. The quotient map used in adic lifting
induces exactly the closed-point morphism `Spec.algebraMap A (ResidueField A)` used in the
target, so both clauses apply to the stated special fibres.

For the closed-immersion clause the reduction applies
[`MultiplicativeTypeLocalClosed.isClosedSubgroup_of_isotrivial`](MultiplicativeTypeLocalClosed.md)
with the same splitting cover. Over that cover the proof obtains surjectivity of the
Hopf coordinate map from surjectivity at the maximal residue fields of the finite splitting
algebra, all lying over `k`. It then descends the closed immersion along the surjective
étale cover.

## Source

Brian Conrad, *Reductive group schemes* (2014), Corollary B.3.5 and its proof,
pp. 292–293, registered as `conrad-2014-reductive-group-schemes` (SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`). As Conrad notes,
the lifting and conjugacy assertions are the complete-local case of SGA 3, Exposé IX,
Corollaire 7.3. The formal proof of closedness uses the coordinate argument above,
not Conrad's fibrewise kernel argument.
