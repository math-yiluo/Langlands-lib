# Compact open identity neighborhoods on actual finite adelic points

`FiniteAdelicGroupCompactOpenBasisStatement` concerns the original
`FiniteAdelicGroupPoints F G` of an arbitrary affine group scheme over a
number field. Its first conclusion is total disconnectedness of the
existing global-regular-function evaluation topology. This conclusion
does not require local finite type.

With `LocallyOfFiniteType G.X.hom`, the second conclusion is a
`Filter.HasBasis` for the identity neighborhood filter, indexed by the
actual open subgroups whose original underlying sets are compact. Thus
every identity neighborhood contains such a subgroup, and any set
containing one is an identity neighborhood.

There is no connectedness, reductivity, splitting, rank or chosen matrix
representation premise. The coefficient ring is the actual restricted
finite adele ring and the point group retains its existing topology and
group operations. Neither discreteness of rational points nor any
assertion about the full adelic or archimedean point topology is made.

This is an internal specialization target, rather than a new assertion
attributed to external literature. The intended route uses the pinned
Mathlib ultrametric topology of the actual finite completions, the
continuous injective map from the restricted finite adeles to their full
product, and the published affine coordinate evaluation embedding. The
published local compactness of actual finite adelic points and the
Library's general Van Dantzig theorem then give the subgroup basis. This
pair only states the proposition; its proof requires a separate focused
exact-target task after publication.

The basis supplies finite-level topology for later automorphic smoothing.
It does not assert smooth vectors, density, archimedean regularity,
growth, a tensor-product realization, trace or spectral decomposition.
