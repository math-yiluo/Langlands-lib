# Normalized covariant fixed vectors from unipotence

This internal derived construction uses the defining fixed-vector property
of `IsUnipotent` and the preceding `CovariantRegularFixedLine` results.
No external theorem is invoked. The field `k : Type u` has arbitrary
universe, and all invariance and product-cell conditions quantify over
every original relative scheme test.

Supply affine group schemes `G` and `H`, a group scheme `U`, actual
homomorphisms `i : H → G` and `j : U → G`, and a coordinate `χ` on `H`.
Supply a nonzerodivisor coordinate `q` on `G` such that every test point
where `q` is a unit factors as `i(a) j(u)`. Neither `χ` being a character
nor `U` being affine is required.

`eq_zero_of_covariant_rightInvariant_counit_eq_zero` proves that a
left-covariant, right-invariant coordinate with zero counit is zero.
On the supplied product cell, right invariance removes `j(u)` and
covariance computes the remaining value as `χ(a)` times the counit.
The preceding nonzerodivisor separation theorem extends vanishing to
the entire coordinate algebra.
`counit_ne_zero_of_covariant_rightInvariant` is the contrapositive.
These two results do not require unipotence.

For
`affineRegularRepresentation_exists_normalized_fixedVector`,
add the unipotence of `U`, a nonzero covariant regular subspace `V`,
a finite basis `b`, and stability under every coalgebra right action.
Unipotence supplies a nonzero vector fixed by the actual regular
representation restricted through `j`. Its coordinate is nonzero
by injectivity of the basis map. Fixedness gives right invariance,
so the preceding vanishing result makes its counit nonzero.
Rescaling the vector by the inverse counit gives a fixed vector
with coordinate counit one. The preceding fixed-line theorem then
identifies the entire restricted fixed submodule with its span.
No normalized fixed vector or normalized covariant is assumed.

`affineRegularRepresentation_exists_fixedVector_of_normalized_covariant`
additionally supplies a normalized right-invariant covariant coordinate
`f`, without assuming `f ∈ V`. Geometric uniqueness identifies `f`
with the coordinate of the fixed vector just constructed. Thus `f`
belongs to every such nonzero regular subspace, and the theorem returns
a vector representing it, its all-test fixedness, and the entire
fixed-submodule equality.

`affineRegularNormalizedFixedVector` chooses the normalized fixed vector
from the existence theorem. Its `_spec` theorem records its all-test
fixedness, coordinate counit one, and entire fixed-submodule equality.

The results apply when `V` is the entire covariant space if its finite
basis is supplied. They do not construct a product cell, prove
finiteness of an entire covariant space, prove that a fixed vector's
orbit spans that space, or establish cofinal Steinberg irreducibility.
