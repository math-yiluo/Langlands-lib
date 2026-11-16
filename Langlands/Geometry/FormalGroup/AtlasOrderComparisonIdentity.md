# Identity comparisons on actual refinements and their coefficient extension

This internal module defines `Comparison.diagonal E q` as the actual
identity formal isomorphism of the order atlas obtained by restricting
`E` to the specified principal-cover refinement `q`. Both sides use
that same refinement. The predicate `IsDiagonal` records that an
existing specified self-comparison equals such a diagonal comparison.
It retains the actual coordinate isomorphism, not just its action on
point families.

The scalar and coefficient rings are arbitrary commutative rings with
their given algebra structure, the acting order is any algebra ring,
and coordinate types are finite. Covers may be infinite. Test algebras
use the coefficient-ring universe.

The supporting isomorphism laws follow from extensionality of the
forward formal map and the stored identity and inverse equations.
`diagonal_baseChange` uses the actual construction of comparison
coefficient extension: its conjugate of the extended identity reduces
to the identity by these inverse equations. Its resulting refinement
is exactly `q.baseChange S`. Existential elimination then proves
`IsDiagonal.baseChange`. The ordinary reflexive comparison is diagonal
on its ordinary reflexive refinement.

The provenance is internal from the existing actual formal-map,
refinement and coefficient-extension constructions. No formal
comparison is replaced by a point-functor equivalence, and this module
does not identify coefficient extension of a reflexive refinement with
the canonical reflexive refinement.
