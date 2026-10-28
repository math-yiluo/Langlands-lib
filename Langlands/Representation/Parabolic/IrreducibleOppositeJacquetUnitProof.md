# Irreducible opposite-Jacquet unit embeddings: proof

Author: Worker 166.

`Langlands.Parabolic.irreducibleOppositeJacquetUnit` proves the exact
`Langlands.Parabolic.IrreducibleOppositeJacquetUnitStatement.{uF,uV}`. The field
and inducing-carrier universes remain independent. The theorem assumes no
additional condition beyond those in the statement and covers both the standard
and arbitrary refined cases.

The private lemma `embedding_of_endomorphism_equiv` isolates the algebraic
argument. Suppose `σ` is irreducible, `ρ` has a nontrivial carrier, and a complex
linear equivalence identifies endomorphisms of `ρ` with intertwiners `σ → τ`.
The identity of `ρ` is nonzero: evaluate a putative equality to zero at a nonzero
vector. A linear equivalence preserves and reflects zero, so its image is a
nonzero intertwiner. The irreducible-source theorem
`Representation.IsIrreducible.injective_or_eq_zero` makes that image injective.

In the standard case, irreducibility first gives a nontrivial inducing carrier.
The published
`CuspidalSupport.normalizedParabolicInduced_eval_surjective` says that evaluation
at the identity from the actual normalized induction to this smooth inducing
carrier is surjective. Its nontrivial target makes the induced carrier
nontrivial. That existing result uses compact local sections, inflation through
the continuous Levi projection, and twisting by the actual positive half-modulus
with open kernel. The proof reuses the published result directly.
`normalizedInductionAdmissibility` makes this induction admissible.

In the refined case, irreducibility again gives a nontrivial inducing carrier.
`normalizedRefinedInductionNonvanishing` directly supplies nontriviality of the
actual normalized refined induction. The published
`normalizedRefinedInductionAdmissibility` supplies its admissibility, for an
arbitrary representation of the refined Levi.

For each case, instantiate the corresponding conjunct of the published
`normalizedSecondAdjointness.{uF,uV,max uF uV}` with ambient representation
equal to the induction itself. Both inputs are admissible. Its linear
equivalence identifies endomorphisms of the induction with intertwiners from
`σ` to its actual opposite normalized Jacquet module. Applying the private
lemma gives the required injective map. Naturality of the chosen family is
unneeded for this existence assertion.

This is an internal derivation from published second adjointness, admissibility,
compact-section and irreducibility results. It selects no canonical embedding
and establishes no constituent multiplicity formula, quotient-detection result
or irreducible-head theorem.
