# Closed matrix realizations of actual infinite-place points

Author: Worker 1359.

This internal prerequisite assembles the published closed linear embedding
theorem, the closed-immersion theorem for actual affine points, and the
homeomorphism between actual general-linear scheme points and matrix units.
It makes no new assertion from the literature. Its provenance is the
composition of those existing constructions and their topology comparisons.

For a matrix representation `ρ` of an arbitrary group scheme over a
commutative ring `R`, `MatrixRepresentation.continuous_affineMatrix` proves
continuity on actual coefficient points. Only a topology on the coefficient
algebra `A` is needed: postcomposition with the scheme morphism is continuous
in the regular-function evaluation topology, and the published general-linear
point equivalence is continuous into the matrix-units topology. The map
`affineMatrixContinuous` packages this very same homomorphism as a continuous
group homomorphism.

If the source scheme is affine, `A` is a Hausdorff topological ring, and `ρ`
is a scheme-theoretic closed linear embedding,
`isClosedEmbedding_affineMatrix` proves that the coefficient map is a closed
topological embedding. It first uses
`isClosedEmbedding_affinePointsTarget` for the actual closed immersion and
then composes with `GeneralLinear.affinePointsHomeomorph`. Consequently it
is injective and has closed image. Its source topology remains the existing
regular-function evaluation topology; its target is the existing group of
units in the matrix ring, with the topology recording the matrix and its
inverse. The argument includes the empty matrix index type.

In `Langlands.Global.InfinitePlaceGroupPoints`, `matrixHom G ρ v` specializes
this continuous homomorphism to the actual completion `v.Completion`. Its
domain is literally `InfinitePlaceGroupPoints F G v`, and the application
lemma identifies it with `ρ.affineMatrix (CommAlgCat.of F v.Completion)`.
No coefficient field, point carrier, or topology is replaced.

For any field `F : Type u`, `exists_closedMatrixRealization_of_finiteType`
assumes that the actual structure morphism of `G` is affine and locally of
finite type. The published `affineLinearEmbeddingStatement` constructs a
natural number `N` and an actual representation
`ρ : MatrixRepresentation G (Fin N)` that is a closed immersion of schemes.
The generic closed embedding lemma then applies at every infinite place
using the existing Hausdorff topological field structure on its completion.
One algebraic representation works for all those places.

Finally, `exists_closedMatrixRealization` obtains both algebraic hypotheses
from the existing `IsConnectedReductive G`: affineness is its recorded
property and smoothness implies local finite type. It retains arbitrary
universe `u` and requires only `Field F`, so in particular it applies to
every number field in the Iwasawa target. Neither a representation nor
analytic comparison data is supplied as an additional hypothesis.

This result constructs an ordinary faithful closed matrix realization. It
does not prove that its image is stable under conjugate transpose, that polar
factors belong to that image, or that a parabolic range times a compact
subgroup covers it. Maximal compact subgroup existence and the full
`ParabolicIwasawaStatement` remain separate proof obligations.
