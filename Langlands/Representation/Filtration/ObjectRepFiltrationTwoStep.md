# Two-step filtration from irreducible subspace and quotient

This internal construction is derived from the published `LengthTwo.twoStep`
construction and `FunctorLengthTwo.nonempty_quotientBot_equiv`. It is a small
assembly construction for the juxtaposed-segment proof, rather than a new
representation-theoretic input.

For an arbitrary representation over a field, let `K` be an invariant subspace.
If its restricted representation and the actual successive quotient
`LengthCriterionProof.quotientRep K ⊤` are irreducible,
`Langlands.LengthTwo.irreducibleTwoStep` constructs the
filtration `0 ⊆ K ⊆ V`. Its middle step equals `K`, its lower graded
representation is actually equivalent to the restriction to `K`, and its upper
graded representation is actually equivalent to that same quotient. Both
factors are simple. The result is a subtype consisting of the actual filtration
and proofs of those properties. `irreducibleTwoStep_filtration` identifies the
underlying filtration with `LengthTwo.twoStep K` by reflexivity.
`exists_twoStep_of_irreducible` is its existential form.

The proof uses the existing two-step filtration. The bottom quotient is
equivalent to `K` by the published quotient-by-zero lemma, so its
irreducibility follows by transport. The equivalence for the top factor is the
identity, and the middle-step equality holds by definition.

The construction works for an arbitrary field, monoid, and module, with
independent coefficient, monoid, and representation universes. It assumes
irreducibility only of the two supplied representations; it adds no assumptions
to any p-adic classification statement.

The imports are `FunctorLengthTwoDetection` and its transitive algebraic
filtration and smooth-subquotient infrastructure. The used results
`LengthTwo.twoStep`, `LengthTwo.isIrreducible_of_equiv`, and
`FunctorLengthTwo.nonempty_quotientBot_equiv` concern actual quotient modules
and transport of irreducibility. No p-adic, classification, Jacquet,
derivative, or segment result is used. Thus this helper is independent of every
classification exclusion in task `0c90f7e4-78fa-43fd-8736-238bb3e8617d`.

Worker 1032 proposed the required interface in the joint proof plan; Worker 167
implemented this construction.
