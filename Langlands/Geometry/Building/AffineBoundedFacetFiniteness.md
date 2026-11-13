# Finitely many facets meeting an affine bounded set

These internal results concern an arbitrary real affine torsor `A` and a
corrected affine root system `Ψ`, including rank zero. A subset `Ω` is bounded
in the sense used here when the image of `Ω` under every real affine function
is bounded above.

`exists_bound_linear_vsub` applies this hypothesis to a derivative coordinate
and its negative, relative to any chosen origin. It bounds the absolute value
of that coordinate on `Ω`.

`IsAffineRootSystemWithRankZero.finite_facets_meeting` proves that the set
`facet Ψ '' Ω` is finite. For a chosen origin `p`, the published theorem
`finite_bounded_at` gives finitely many roots whose value at `p` is no larger
in absolute value than the corresponding coordinate bound. Every other root
has constant sign on `Ω`. Restricting signs to the finite root set therefore
injects the facets meeting `Ω` into a finite set of sign patterns.

`finite_vertices_of_facets_meeting` additionally uses a finite dimensional
normed translation space. The published finite vertex encoding of each
closed facet, and the preceding finite set of facets, show that the union of
their full vertex sets is finite.

`boundedFacetVertexFinset` encodes exactly this union as a finset. Its membership
theorem removes any dependence on the choices used in the proof.
`boundedFacetVertexFinset_nonempty` shows that it is nonempty whenever `Ω` is
nonempty, including for the affine root system of rank zero.

The provenance is internal: these are consequences of the published
corrected affine root axioms, facet sign definitions, and finite torsor
vertex theorem. They isolate the apartment finiteness step needed in the
geometric proof route to KP 8.3.1--8.3.2. They do not assert any building
axioms, quotient fixer containment, or normality statement.
