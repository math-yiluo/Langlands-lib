# Maximal tori through a homomorphism with a common geometric maximal torus

This internal result concerns an actual homomorphism `q : H → Q` over a field
`k`. The source is smooth, connected and affine, and the target is affine.
Let `K/k` be any algebraically closed field extension in the same arbitrary
universe. Suppose there is a commutative group scheme `S` over `K` and a map
`s : S → H_K` which is a maximal torus in `H_K` and whose composite with `q_K`
is a maximal torus in `Q_K`.

`CommonGeometricMaximalTorusHomStatement` concludes that every maximal torus
`i : T → H` over `k` has `i ≫ q` maximal in `Q`. It also constructs an original
field torus and map which are maximal both before and after composition.
The source of each torus map is retained exactly. There is no assumption that
`q` is a quotient or a closed immersion, and no smoothness, connectedness or
finite type assumption on `Q`. The field `k` need not be perfect, and either
characteristic is allowed. The geometric common-torus witness is an explicit
hypothesis.

The first helper,
`MaximalToriAreConjugate.isMaximalTorus_comp_of_common`, works over any field
where the maximal tori of `H` are conjugate by rational points. A given source
maximal torus is conjugate to the reference maximal torus `s`.
`SubgroupConjugate.postcomp` transports this conjugacy through the arbitrary
homomorphism `q`. `SubgroupConjugate.isMaximalTorus_iff` transfers maximality
from `s ≫ q` to the original composite. This uses the existing predicate for
maximality among all closed tori, including nonsplit tori.

`IsMaximalTorus.comp_of_common_geometric_maximalTorus` applies this argument
over `K`. The published `maximalTorusBaseChange` makes the base change of any
original maximal torus maximal in `H_K`. The published
`connectedSpace_baseChange_of_smooth_affine` gives connectedness of `H_K`;
smoothness and affineness follow by base change. The published
`maximalTorusConjugacy` therefore supplies the required conjugacy over `K`.

The resulting geometric composite is a maximal torus and hence a closed
immersion. `IsClosedSubgroup.of_baseChange_of_isAffine` reflects this closed
immersion through the flat surjective field-extension base map. Its affine
source comes from the original closed torus in the affine group `H`.
`IsMaximalTorus.of_baseChange` then reflects maximality over the same
extension. Thus no closedness premise on the original composite is retained.

Finally, the published `maximalTorusExistence` gives a maximal torus in `H`
over `k`. The preservation theorem proves maximality of its composite.
`commonGeometricMaximalTorusHom` assembles these two conclusions into the
universal proposition.

The provenance is internal composition of published Library results. The
inputs are `Torus.MaximalTransport`, `Rational.SubgroupConjugacy`,
`Torus.MaximalBaseChangeProof`, `Torus.MaximalBaseChangeReflection`,
`Absolute.MaximalTorusConjugacyProof`, `Torus.ExistenceProof`,
`GeometricConnectedness`, and `Descent.ClosedSubgroups`.

For an eventual segment-model application, a common geometric maximal torus
must still be constructed for the actual special-fibre map. This result
constructs no building, coherent model family, comparison map, residue torus
lift or special apartment, and does not prove
`UnramifiedFixedPointSplitTorusStatement`.
