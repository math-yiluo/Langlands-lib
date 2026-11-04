# The zero weight of a self-centralizing commutative subgroup

This internal construction identifies the actual Lie kernel of a monomorphic
commutative subgroup with the zero adjoint weight space when that subgroup is
its own centralizer on every test scheme. The self-centralizer equality is an
explicit input. This file does not prove the maximal-torus centralizer theorem
or the central-isogeny root-datum theorem.

Let `R : CommRingCat.{u}`, let `T` be a commutative group scheme over `Spec R`,
and let `G` be a group scheme over the same base. Both structure morphisms are
affine. The constructions use the actual dual-number identity kernels
`lieKernel T.toGrp R` and `lieKernel G R`, with their published module structures.
No splitness, smoothness, field, reductivity or maximality is needed here.

The differential of `i : T.toGrp ⟶ G` is postcomposition on actual dual-number
points. Since the image of a commutative group scheme centralizes itself on all
test schemes, that differential lands in `weightSpace i 0`.
`Lie.zeroWeightMap i` is this linear map with the restricted codomain, and its
computation lemma states that its underlying map is `Lie.targetMapLinear i R`.
Monicity of the underlying morphism in `Over (Spec R)` makes it injective.

Suppose that `torusCentralizer i = SubgroupFunctor.range i`. The published
comparison in `Lie.TorusCentralizer` says that a zero-weight Lie vector is a
dual-number point lying in this all-test centralizer. The equality therefore
factors that point through `T`. Its reduction maps to the identity in `G`;
monicity of `i` forces the reduction in `T` to be the identity as well.
Thus the factoring point is in the actual Lie kernel of `T`, proving
surjectivity of `Lie.zeroWeightMap i`.

`Lie.zeroWeightEquivOfSelfCentralizing i hself` packages these two implications
as an `R`-linear equivalence. Its forward map is the original differential.
Over an arbitrary field, `Lie.finrank_zeroWeight_of_selfCentralizing` equates
the finite ranks of the zero weight and the subgroup's actual Lie kernel.
This numerical equality is valid without an additional finite-dimensional
hypothesis, since it follows from a linear equivalence.

The provenance is internal: the proof combines the existing all-test
centralizer/zero-weight comparison, the elementary self-centrality of a
commutative image, and the published reflection of reduction through a
monomorphism. It does not invoke a literature structure theorem. In the
central-isogeny application, deriving the self-centralizer equality for the
supplied maximal tori remains a separate geometric obligation.
