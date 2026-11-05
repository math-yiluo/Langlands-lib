# Coordinate-smooth families of finite products of group schemes

This internal construction assembles smooth parameter families in the actual
categorical finite product of affine group schemes. It uses the published
`CoordinateSmooth` criterion, which tests every global regular function after a
specified coefficient map. It does not introduce a manifold structure on a
general group of scheme points.

For a scheme `S`, a finite index type `J`, and group schemes `G j` over `S`,
`piFactorInclusion G j` is a genuine map of relative schemes from the `j`th
factor to `pi G`. Its `j`th projection is the identity map, and every other
projection is the group identity. These maps are defined by the universal
property of the actual product. The two projection formulas are proved.

`piPointsEquiv_symm_eq_list_prod` expresses any family of points, on any test
scheme over `S`, as the ordered product of its factor insertions. Its list must
contain each index exactly once. The proof applies each product projection,
uses its multiplication law, and observes that all terms except the matching
factor are the group identity. This works for noncommutative point groups and
also permits an empty index type.

For a base commutative ring `R`, assume every `G j` is affine and let `A` be any
commutative `R`-algebra in the same universe. The coefficient map
`c : A →+* B` has values in a normed commutative real algebra `B`; it need not
be an algebra homomorphism. The parameter space `M` is any charted space with a
real model with corners `I`. The index and base ring share a universe, while
the target normed algebra and parameter space have independent universes.

`isAffine_pi` proves affineness of the actual product using the published
finite-product stability theorem for affine structure morphisms and the affine
base `Spec R`. The proof of `coordinateSmooth_piPointsEquiv_symm` postcomposes
each smooth factor family with its actual insertion map and applies the
published smooth multiplication theorem repeatedly. The point reconstruction
formula identifies the resulting ordered product with the actual assembled
family.

`coordinateSmooth_groupSchemePi_iff` states that a family of product points satisfies the
all-regular-function criterion exactly when each projected factor family
satisfies it. The forward implication pulls regular functions back along the
actual projection maps. The reverse implication is the assembly theorem.
`coordinateSmoothPiEquiv` restricts the published equivalence of actual points
to an equivalence of these smooth parameter families. Its inverse laws follow
from those of the original point equivalence.

The provenance is internal: this is a consequence of the published product
universal property, regular-function pullback, affine multiplication criterion,
and Mathlib's ordered product identities. No new identification with an
original-literature theorem is claimed. It concerns products of group schemes
over one base, with one test algebra. Analytic differentiation of a scheme
representation, its comparison with the dual-number differential, and
automorphic coefficient cohomology require further constructions.
