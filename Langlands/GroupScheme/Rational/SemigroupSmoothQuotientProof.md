# Smooth quotients of the actual semigroup subgroup functors

Worker 1345 assembles this proof using the functoriality construction and route
shared with Worker 1372.

`Langlands.GroupScheme.RelativeRoot.semigroupSmoothQuotient` proves exactly
`SemigroupSmoothQuotientStatement.{u}` at every universe `u`. For a smooth
equivariant surjection between smooth affine group schemes over any field,
every additive subsemigroup of the original split torus's character lattice
and every pair of representatives of the actual semigroup subgroup functors
admit a homomorphism with the prescribed ambient composite. This induced
homomorphism is smooth and surjective as a morphism of schemes. The ambient
groups need not be connected, and the semigroup may contain zero or be empty.

The source assertion is the smooth-quotient paragraph following Example 3.3.7
in Conrad–Gabber–Prasad, *Pseudo-reductive Groups*, second edition (2015),
printed p.111 / PDF p.137, registered as
`conrad-gabber-prasad-2015-pseudo-reductive`, SHA256
`1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`.
The implemented proof composes published results through
`semigroupSmoothQuotient_of_realization_functoriality_differential`:

1. `semigroupRealization` supplies smooth connected closed representatives
   and their exact selected Lie images.
2. `semigroupFunctoriality_of_imageGeneration_and_containment` supplies
   functorial containment. Its two premises are discharged by
   `ImageGeneration.pointedImageGeneration` and the containment component
   `CoordinateWeights.coordinateSemigroupComparison.2`. Thus containment
   holds on every test scheme without a separability assumption on the map.
3. The reduction lifts postcomposition to the given representatives and
   proves the ambient commutative diagram. Smoothness of the original map
   makes its actual differential surjective on each selected weight span.
   The representatives' exact Lie images then give a surjective actual
   differential for the induced homomorphism.
4. `Lie.smoothSurjectiveOfSurjectiveDifferential` applies to the induced
   map. Its source and target are smooth affine groups and its target is
   connected by realization. It concludes actual scheme smoothness and
   surjectivity.

All three proposition premises of the reduction are discharged by proved
theorems. The final theorem has no additional proposition premise. The
original map's surjectivity hypothesis is preserved by the exact statement,
although the reduction only needs its smoothness. This proves the smooth
quotient component; the full comparison task also requires its functoriality
and three-alternative intersection components.
