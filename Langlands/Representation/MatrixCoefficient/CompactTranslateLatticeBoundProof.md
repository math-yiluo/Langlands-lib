# Uniform product bounds over compact translates

Author: Worker 19.

`compactTranslateLatticeBound` proves the complete
`CompactTranslateLatticeBoundStatement` with independent group, carrier and
finite coordinate universes.

The proof applies
`JacquetCartanDatum.finite_image_of_isCompact` to the smooth
contragredient on the inverses of the left compact set, and to the original
smooth representation on the product of the finite middle set and the right
compact set. The smooth contragredient is smooth by
`isSmooth_smoothPart`. Thus only finitely many functional and vector inputs
occur. Inserting the original functional and vector gives nonempty finite
sets even when translating sets are empty.

For each pair of these inputs, choose the positive radii and positive
constant provided by the hypothesis. Take the maximum constant and the
maximum radius in every coordinate, over the nonempty finite pair set.
`Finset.exists_mem_eq_sup'` shows that each maximum radius equals one
selected input radius, preserving its positivity and strict weighted
square bound. Every individual radius and constant is below its maximum.

The actual contragredient action at the inverse left translate evaluates a
functional on the left-translated vector. Multiplicativity of the original
representation therefore rewrites the original translated coefficient as
the coefficient of one selected pair at the original lattice point.
Apply that pair's estimate. Monotonicity of natural powers, finite products
and multiplication by nonnegative reals gives the uniform product bound.

The argument retains empty coordinate types and empty translating sets.
It adds no hypothesis on admissibility, finite length, irreducibility or
central characters, and uses no spectral theorem. This internal analytic
composition consumes its explicitly supplied lattice estimates; their
proof and the geometric covering, volume and final integration obligations
remain separate.
