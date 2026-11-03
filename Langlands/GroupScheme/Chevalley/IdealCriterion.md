# The ideal criterion for a finite subspace stabilizer

This internal algebraic step follows the ideal argument in Milne, *Algebraic
Groups* (2017), Theorem 4.27. Let `r : B → C` be a surjective homomorphism of
commutative bialgebras over a field. Let `V` be a regular subspace of `B`
containing a finite set of ideal generators of `ker r`, and let
`W = V ∩ ker r`, named `idealSubspace V r.toLinearMap` in Lean.

The main equivalence `stabilizes_iff_factors` says that a point `f : B → A`
translates every element of `W` into its actual scalar extension in `B ⊗ A`
if and only if `f` factors through `r`. The coefficient algebra `A` is an
arbitrary commutative algebra, including nonreduced algebras.

The forward proof applies the counit on `C` to a translated generator,
recovering its value under `f`. Thus `f` kills every ideal generator, hence
the full kernel, and descends through the surjection `r`. Conversely,
bialgebra compatibility shows that translation by a point factoring through
`C` preserves the kernel. The regular-subspace result preserves `V`.
Exactness of tensoring over a field identifies the intersection of these two
scalar extensions with the scalar extension of `W`.

`exists_finite_subspace_stabilizer` uses `regularSpan` on the ideal generators
to supply one finite-dimensional `V` whose criterion holds for every coefficient algebra. This is the algebra-test subspace
criterion. A group-scheme representation, its projective line construction,
and its comparison on arbitrary scheme tests are later steps.
