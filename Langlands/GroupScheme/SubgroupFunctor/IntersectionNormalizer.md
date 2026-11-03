# Normalizers of subgroup intersections

This internal helper composes the published subgroup functor, all-test normalizer
and preimage constructions. It supports the Borel normalizer induction when an
internal subgroup of a centralizer represents the actual intersection with a
Borel subgroup. It does not assert that such an intersection is Borel, or that
points determine a subgroup scheme.

`inf_normalizer_le_normalizer_inf` proves that a point normalizing two subgroup
functors normalizes their intersection. The proof applies both given normalizer
conditions after each refinement, in each direction of conjugation.

`comap_normalizer_le` proves that a point whose image under a group-scheme
homomorphism `j : H ⟶ G` normalizes `F` normalizes the preimage `F.comap j`. The
proof uses preservation of products and inverses under composition with `j`.
No monomorphism hypothesis is required for this inclusion.

`normalizerComapHom j F U` is the corresponding inclusion homomorphism from
`(F.normalizer.comap j).carrier U` to `(F.comap j).normalizer.carrier U`.
It applies `Subgroup.inclusion` to `comap_normalizer_le` on `U` and preserves
the underlying point. It is defined over every base scheme without a
monomorphism hypothesis on `j`.

Suppose `c : C ⟶ H`, `j : H ⟶ G`, the underlying morphism of schemes over the base
of `j` is monic, and
`range (c ≫ j) = range j ⊓ F` on all test schemes.
`range_eq_comap_of_range_comp_eq_inf` identifies `range c` with `F.comap j`.
One implication follows from the given intersection equality. For the other,
that equality provides a lift through `c ≫ j`; cancellation of the monomorphism
`j` identifies its image through `c` with the original point.

`mem_normalizer_of_range_comp_eq_inf` applies this identification and the
preimage normalizer inclusion. Thus a point of `H` whose image normalizes `F`
normalizes `range c`, with normalizer membership tested on every refinement.

`mem_pointNormalizer_of_range_comp_eq_inf` gives the corresponding conclusion
for the abstract normalizer of the point subgroup on one test scheme `U`. Its
proof uses the same preimage identification and Mathlib's
`Subgroup.le_normalizer_comap` for the homomorphism on `U`-points induced by `j`.
It applies in particular to ground-field points and does not require a bridge
from an abstract point normalizer to the all-test normalizer functor.

All results hold over an arbitrary base scheme, in an arbitrary universe.
They are derived from the imported constructions and elementary group and
category laws; no additional literature theorem is used.
