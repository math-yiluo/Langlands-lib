# Central differences of split-torus homomorphisms

This internal unit supplies three related helpers for the direct rank-one
argument. It uses the actual group-scheme maps and all scheme tests.
Its provenance is the existing automorphic-action, pointwise Yoneda and
split-torus-to-unipotent vanishing constructions, rather than an assertion
quoted from the literature.

`AutomorphicAction.isCentral_comp_of_character_eq_zero` works over an arbitrary
base scheme. Suppose conjugation by `i : T → G` is the restriction of an actual
automorphic action of the multiplicative group along a character `a` of `T`.
For any homomorphism `f : H → T` killed by `a`, it proves that `f ≫ i` is central.
The proof evaluates the descended-action equality after an arbitrary refinement
of an arbitrary scheme test. The character value is the identity, so the action
is trivial and the two group elements commute. No splitness or nonzero-character
assumption is needed for this implication.

For homomorphisms `s,b : D → G` with `b` central,
`Dynamic.centralDifferenceHom s b hb` is the actual homomorphism whose value at
`x` is `s(x) * b(x)⁻¹`. Centrality permits the rearrangement needed to prove
multiplicativity. The point maps commute with pullback, so `homOfPoints`
constructs the group-scheme homomorphism.
`Dynamic.centralDifferenceHom_apply` records its value on every scheme test.

Over an arbitrary field, `Dynamic.splitTorus_eq_of_central_difference_unipotent`
assumes that `D` is a split torus, that an affine group scheme `U` is unipotent,
and that a homomorphism `j : U → G` represents its range subgroup functor. If
`s(x) * b(x)⁻¹` belongs to that range on every scheme test, it proves `s = b`.
The proof factors the central-difference homomorphism through `j`, applies the
existing vanishing theorem for homomorphisms from split tori to unipotent groups,
and cancels in each group of points.

These are preliminary helpers. They do not prove parabolic torus conjugacy,
rank-one two-cell covering, opposite factor-pair existence, or the host task's
unconditional factorization statement.
