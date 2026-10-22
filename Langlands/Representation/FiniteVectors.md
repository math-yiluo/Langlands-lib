# Finite vectors in actual representations

For a field `k`, a monoid `G`, and a representation `ρ` on a `k`-vector
space `V`, `orbitSpan ρ v` is the linear span of the actual vectors `ρ g v`.
The field, monoid and vector spaces have independent universes.
`IsFiniteVector ρ v` means that this span is finite dimensional.
The ambient vector space may have arbitrary dimension and has no topology.

`orbitSubrepresentation` proves stability by induction on the linear span,
using multiplication in the monoid for orbit generators. The identity element
puts the original vector in its orbit span. `orbitSpan_le` proves minimality
among invariant subspaces containing that vector. Consequently finite vectors
are exactly the vectors lying in some finite-dimensional subrepresentation.
Finite-dimensional superspaces give closure under addition, scalar multiplication
and the original action. `subrepresentation` and `representation` bundle this
subspace and restricted action; `inclusion` is the injective equivariant inclusion.

For an intertwining map, `map_orbitSpan` identifies the image of an orbit span
with the orbit span of the image vector. It follows that equivariant maps
preserve finite vectors; injective equivariant maps also reflect finiteness.
The reflection proof restricts the injection to the two actual orbit spans.
`map` restricts an intertwiner to finite vectors, and `inclusion_map` records
its compatibility with the ambient inclusion.

This is a derived algebraic prerequisite for the compact-finiteness condition
in A. Borel and H. Jacquet, “Automorphic forms and automorphic representations,”
Corvallis Part I (1979), §1.5(1), printed p.190, one-based PDF p.185.
That passage defines right compact finiteness by the finite-dimensional span
of right translates. The original is registered as
`borel-jacquet-1979-automorphic`; SHA256
`3b9fe0145da81d870ef8967be83635cd440a2581fe043e64e63324e22dec4db5`.
The original page was read directly. The extension to arbitrary algebraic
monoid representations and the constructions above are elementary derivations,
not assertions that the source states this exact general API.

This module proves no compactness, complete reducibility, density or
finite-dimensionality of the entire finite-vector space. In an application to a
subgroup, the restricted action is only that subgroup's action; invariance under
an ambient larger group requires its own argument.
