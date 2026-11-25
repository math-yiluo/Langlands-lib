# Coordinate subspaces and chamber topology

Module
`Langlands.Representation.LanglandsClassification.ParabolicChamberBasis`,
namespace `Langlands.GroupScheme.ParabolicChamberAux`.

These are internal derived linear-algebra and topology helpers for the parabolic
chamber proof. They use Mathlib's bases, submodules, complementary subspaces,
finite-dimensional real topological vector spaces and product topology. They
introduce no new statement about reductive groups and have no separate
literature claim.

`restrict_basis` restricts an ambient basis to a set of indices when the selected
vectors lie in a submodule and all other coordinates vanish on that submodule.
Independence follows from ambient independence and injectivity of subtype
inclusion. The coordinate-support criterion puts every submodule vector in the
span of the selected vectors. Mapping their subtype span into the ambient space
then gives spanning inside the submodule. `restrict_submodule_basis` applies
this result within an ambient submodule and transports the resulting basis
through `Submodule.comapSubtypeEquivOfLe`.

`projection_unique` takes `IsCompl P Q` and obtains the unique decomposition
`x = u + v`, with `u ∈ P` and `v ∈ Q`. The first summand is the unique `y ∈ P`
with `x - y ∈ Q`, as required for the Library projection-set definitions.

`repr_eq` shows that functionals with Kronecker values on a basis are its
coordinate functionals: equality of linear maps is checked on the basis.
`sum_eq` identifies the ambient coercion of the inverse coordinate map with the
finite `finsum` of scalar multiples of the basis vectors. For any predicate `p`
on real numbers, `coordinate_set` uses these identities in both directions to
identify vectors satisfying `p` on every coordinate with basis sums whose
coefficients satisfy `p`. `coefficient_set_add` unpacks pointwise set addition
to append a summand to such a coefficient formula.

`orthant_topology` assumes a finite-dimensional real ambient topological vector
space with Hausdorff topology and a basis of a submodule `P` with finite index
type. The inverse basis-coordinate equivalence followed by inclusion in the
ambient space is a closed embedding: finite-dimensional subspaces are closed,
and the coordinate equivalence is a homeomorphism. It identifies the positive
coefficient set with the image of a product of intervals `Ioi 0` and the
nonnegative coefficient set with the image of the product of `Ici 0`. The
finite product of open intervals is open, giving openness relative to `P`.
Closed embeddings preserve closures of images, and `closure_pi_set` together
with `closure_Ioi` gives the ambient closure identity. The proof also covers an
empty coordinate index type.

`moduleTopology_t2` supplies the Hausdorff hypothesis for the canonical real
module topology on any finite-dimensional real space. Choose a basis, give its
index type the finite structure supplied by finite dimensionality, and use its
coordinate equivalence as a continuous injection into the Hausdorff space of
real-valued functions on that finite type. Continuity follows from the defining
property of the module topology.
