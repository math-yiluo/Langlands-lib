# Local occurrence from compact restrictions to fixed spaces

Let an action of a locally profinite group on a complex Hilbert space preserve the inner
product. Suppose a continuous symmetric endomorphism commutes with the action, is compact
when restricted to the fixed vectors of any compact open subgroup, and is nonzero on one
such fixed space. `exists_irreducible_of_compactOnFixedSpaces` produces an irreducible
admissible smooth representation and an injective intertwiner into the Hilbert space.

The fixed space of the chosen subgroup is closed and is preserved by the endomorphism, so the
compact self-adjoint spectral theorem gives a nonzero eigenvalue there. Its eigenspace in
the full Hilbert space is invariant under the local action. The smooth part of that eigenspace
is nonzero. For any open subgroup, choose a compact open subgroup inside it by van Dantzig's
theorem. The fixed space in the smooth eigenspace injects into the finite-dimensional
eigenspace at that compact open level for the same eigenvalue. This proves admissibility.

The given inner product restricts to an invariant positive Hermitian form on the smooth
eigenspace. `admissibleUnitarySemisimplicity` makes its subrepresentation lattice complemented.
Passing to the corresponding semisimple module over the complex group algebra gives an atom
of that lattice. `FiniteIndexRestriction.isIrreducible_toRepresentation_of_isAtom` identifies
its action as irreducible, and `isAdmissible_of_injective` gives admissibility for its inclusion.

This is an internal argument from the compact-operator method used in the Library's
`CompactApproximationEigenspaceProof`. Here a single commuting operator supplies an invariant
eigenspace, while compactness at each compact open level yields admissibility. The input and
output carriers have the same universe.
