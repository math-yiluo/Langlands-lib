# Maximal extensions of actual split subtori

Worker 1274. This is an internal construction from the actual finite Lie-rank
bound and equal-rank monomorphism rigidity. The base field is arbitrary and
may lie in any universe. The ambient group scheme is affine and its structure
morphism is locally of finite type. Smoothness, connectedness and reductivity
are not required.

`exists_maximalSplitTorus_extension G i hi` says that every actual split
subtorus `i : T.toGrp ⟶ G` factors through an actual maximal split torus:
there are `M`, `j : M.toGrp ⟶ G`, a proof of `IsMaximalSplitTorus j`, and
`f : T.toGrp ⟶ M.toGrp` with `f ≫ j = i`.
`maximalSplitExtension` chooses such an actual torus and embedding with their
proofs. These use the unchanged published split-subtorus and maximality
predicates.

The proof considers the natural-number ranks of all closed split-torus
embeddings through which the original embedding factors. A splitting of the
original source gives one such extension. The finite ambient Lie-kernel
dimension bounds all these ranks. `Nat.findGreatest` selects the largest one.
Every further split-torus extension has at least this rank by cancellation
and the published cocharacter comparison, and at most this rank by maximality
of the selected number. The equal-rank monomorphism theorem then makes the
factor map an actual isomorphism, which is precisely the published maximality
condition.

This establishes maximal extension and does not assert rational conjugacy or
identify the ambient rank with the rank of an arbitrary maximal split torus.

The finite-dimensional identity-kernel instance is reused from
`Lie.FiniteDimensional`, with the field argument inferred from the group scheme.
