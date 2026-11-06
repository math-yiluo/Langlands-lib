# Relative homogeneous quotients from exact-fiber maps

Author: Worker 1468.

This internal derived construction generalizes the published field-base
construction in `HomogeneousQuotientFromEmbedding` to every base scheme
`S : Scheme.{u}`. It reuses that module's actual coset relation and
`HomogeneousQuotient` structure, and the published smooth-relation scheme
quotient construction. It introduces no external geometric assertion.

Let `G` be a smooth affine group scheme over `S`, and let `i : H → G` be a
closed subgroup with `H` smooth over `S`. Suppose an actual morphism
`r : G → Y` to a separated `S`-scheme has exactly the right cosets of `H`
as its fibers on every test scheme over `S`. Then
`exists_quotient_of_map_kernel` produces a `HomogeneousQuotient i`:
an actual separated, locally finite type, quasi-compact scheme over `S`,
a smooth surjective quasi-compact projection from `G`, and the exact
right-coset criterion on every test scheme. `quotientOfMapKernel` chooses
such a quotient by classical choice.

The proof applies `schemeQuotientOfMapKernel` to the actual coset relation.
Its quotient has a monomorphic morphism into `Y`, which makes its structure
morphism separated. Local finite presentation descends along the smooth
surjective projection from `G`, and implies local finite type.
For every compact open subset of `S`, its preimage in the quotient is the
continuous image, under the surjective projection, of its preimage in `G`.
The latter is compact because `G → S` is affine and hence quasi-compact.
This proves quasi-compactness of the quotient structure morphism without
assuming that `S` itself is affine or quasi-compact. Quasi-compactness of
the projection follows from quasi-compactness of its composite with the
separated quotient structure morphism. The coset criterion is the
criterion supplied by the smooth-relation quotient and the published
identification of relation sections with subgroup membership.

The ambient exact-fiber map remains a hypothesis. This module does not
construct that map for a relative parabolic subgroup, and it does not
prove properness or the unconditional relative parabolic quotient target.
