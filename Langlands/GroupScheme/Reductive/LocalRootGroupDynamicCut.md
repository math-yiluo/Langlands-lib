# Root subgroups as dynamic intersections over local rings

This internal derived construction compares the actual orbit-extension root
subgroup functor with the intersection of two dynamic subgroup functors. It uses
the published nilpotent-preserving coordinate construction in
`LocalRootGroupFlatCoordinate` and `LocalRootGroupTorusCoordinate`.

For a split-torus homomorphism `i` into a group scheme over `Spec R`, and two
integer cocharacters `mu` and `nu`, `LocalRootGroup.dynamicCut` is the intersection
of the ambient centralizer of `mu` and the ambient positive dynamic subgroup of
`nu`. This definition requires no local, smooth, affine, or fibre hypotheses.

`dynamicCut_le_range_rootMap` assumes an affine ambient group and a polynomial
coordinate of the constructed dynamic root group that is additive on all test
schemes. Each point in the intersection first factors through the represented
centralizer. Its positive-dynamic condition then factors it through the
unipotent subgroup inside that centralizer. The polynomial coordinate identifies
this subgroup with the additive group, giving the asserted root-map factorization.

`subgroup_eq_dynamicCut_of_fibres` assumes a smooth affine ambient group over a
local ring, an exponent `a` with `a(mu) = 0` and `a(nu) = d > 0`, and
`HasEquivariantFibres i mu nu a`. The latter requires an actual additive
parametrization of every field fibre of the constructed dynamic group, equivariant
for the fixed full-torus character `a` on every test scheme over the field. The
conclusion is equality of the actual root subgroup and the dynamic intersection
on every scheme over `Spec R`. No reducedness assumption on `R` is used.

The proof chooses a homogeneous polynomial coordinate using flatness and the
field-fibre hypotheses. Its positive grading makes the coordinate additive.
Full-torus homogeneity gives equivariance and identifies the root map with the
actual root functor. The preceding direct factorization proves containment of
the dynamic intersection in that root functor. The reverse containment follows
from the existing centralizer and positive-dynamic containments for root points.
The proof does not infer equality of morphisms over `R` from equality on its
field-valued points.

`isRepresentedBy_dynamicCut_of_fibres` transfers this equality to any supplied
actual root parametrization. `dynamicCutPointsEquiv` is the resulting
multiplicative equivalence from its additive-group points to the ambient
intersection points on any test scheme; its underlying ambient map is
composition with the supplied root parametrization.

These results are structural prerequisites for comparing root restrictions of
isogenies. They do not assert that a supplied homomorphism has a root-datum
isogeny, or prove the full reductive-isogeny rigidity theorem.
