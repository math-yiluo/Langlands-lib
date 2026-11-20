# Descent from the centralizer of a regular toral Lie element

`RegularTorusDescentStatement` starts with a smooth affine group scheme
`G` over a characteristic-zero field `k` and a maximal torus `T` of its
base change `G_K` to a field extension `K/k`. Suppose `T` centralizes a
Lie element `Y` of `G_K` and its tangent image equals the tangent
centralizer of `Y`. If conjugation by a `K`-point of `G_K` carries `Y`
to the scalar extension of a Lie element of `G`, the same conjugation
carries `T` to the scalar extension of a maximal torus of `G`. The
statement provides an isomorphism of the two tori compatible with their
inclusions and the ambient conjugation.

The implementation represents the Lie-element centralizer as a closed
subgroup and compares it with the representative after scalar extension.
The adjoint equations agree on each affine test. Since both representatives
are affine, testing on each representative gives the two inclusions on
all tests. Ambient isomorphisms transport these adjoint equations by
naturality of the adjoint action.

Cartier's theorem gives smoothness of the ground-field centralizer. Over
the extension, the torus maps into its identity component via the conjugate
inclusion. The differential of this factor is surjective by the tangent
centralizer equality and the injective differential of the enclosing
closed subgroup. A smooth closed subgroup with surjective differential
in a connected smooth group is the whole group. The identity component
commutes with field extension, and torus status and maximality descend.

This is an internal descent step for real approximation. It uses the
published closed adjoint stabilizer, identity component base change,
and maximal torus base change theorems.
