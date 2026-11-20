# Simple quotients and finite families of stable kernels

Let a monoid of operators act on a source and an irreducible quotient, with
an intertwining surjection to the quotient. Restrict both actions along a
homomorphism from a group. A finite family of projections intertwines
this restricted action, and each projection has an operator-stable kernel.
Assume the surjection kills the intersection of these kernels.

Regard the full representations as modules over the operator monoid
algebra. Apply `exists_cyclic_term_quotient` to the quotient maps by the
projection kernels, preceded by the quotient by the zero submodule. This
first map makes the family separate. Selecting it would force a vector
with nonzero quotient image into every projection kernel. The selected
map therefore comes from one of the projections. Its cyclic source has
surjective image in the simple quotient. The equation at the cyclic
generator in the filtration theorem and linearity imply that the
surjection kills the selected projection's kernel on this source.

On restricting the group action, `descendIntertwinerToRange` uses the
quotient by a kernel and its linear equivalence with the actual range.
The descended map is equivariant by applying the original maps to a
representative of a range vector. This gives the actual subrepresentation
of the selected target and the surjective intertwiner required by
`Correspondence.IsSubquotientOf`.

This is an internal algebraic step for choosing a cuspidal Levi summand.
The filtration is the Library's `Langlands.Automorphic.ConstantTermFiltration`.
