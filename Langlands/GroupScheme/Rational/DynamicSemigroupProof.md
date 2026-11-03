# Dynamic functors and their actual cocharacter semigroup subgroups

This module proves the exact published
`Langlands.GroupScheme.RelativeRoot.DynamicSemigroupComparisonStatement.{u}`
from [`WeightSemigroupStatement`](WeightSemigroupStatement.md). The theorem
`dynamicSemigroupComparison` retains every universe `u`, every field, every
smooth affine connected ambient group, every split torus, every homomorphism
from that torus to the group, and every cocharacter, including zero and
nongeneric cocharacters. The equalities hold as subgroup functors on all test
schemes. They identify the Dynamic parabolic, centralizer and identity-limit
functors with the actual generated subgroups for the nonnegative, zero and
strictly positive pairing regions, respectively.

`dynamicUnipotentSemigroupComparison` is already unconditional. It identifies
the actual Dynamic identity-limit functor with the generated subgroup for the
strictly positive pairing region of every cocharacter of a split torus acting
by conjugation. It requires a smooth affine ambient group over a field, but
no connectedness of that ambient group.

The positive Dynamic functor is an admissible generator by the published
closed representative, smoothness, connectedness, exact positive Lie image,
and stability under the original entire torus. It therefore lies in the actual
generated subgroup. Conversely, `positive_generator_le_dynamicUnipotent`
puts every admissible positive generator in that Dynamic functor. The subgroup
closure universal property gives the reverse inclusion, hence equality on every
test scheme.

For the parabolic and centralizer, the auxiliary theorem
`dynamicSemigroupComparison_of_connected` uses the actual closed affine
Dynamic representatives, published smoothness and its explicit
`DynamicConnectedStatement` premise. Their Lie images are the nonnegative and
zero pairing spans by
`dynamicLie` and the cocharacter weight conversions. They are stable under
conjugation by the entire torus. The intrinsic split-torus support theorem
therefore makes each Dynamic functor an admissible generator, yielding the
inclusion into its generated semigroup subgroup.

The reverse inclusions use
`nonnegative_generator_le_dynamicParabolic` and
`zero_generator_le_dynamicCentralizer`. These put every admissible generator
in the corresponding Dynamic functor. They are proved by inducing the action
on a smooth connected subgroup representative and applying a full-Lie criterion
in its actual semidirect product with the multiplicative group. The closure
universal property then gives the inclusions of the generated subgroups.

The auxiliary theorem combines these arguments with the positive equality.
The final theorem `dynamicSemigroupComparison` applies it to the published
`Langlands.GroupScheme.dynamicConnected`, imported from
[`Dynamic.ConnectedProof`](../Dynamic/ConnectedProof.md). Thus the final theorem
has exactly `DynamicSemigroupComparisonStatement.{u}` as its type, with no
additional premise.

The provenance is internal. The proof assembles the actual Dynamic geometric,
Lie and stability results with intrinsic torus support and generated subgroup
closure. There is no reductivity, maximality or chamber hypothesis, and the
proof assumes neither the general semigroup realization statement nor
uniqueness of a subgroup with a prescribed Lie image. Worker 1284 assembled the
containment and comparison proofs; Worker 1301 supplied the weight-span adapter
draft used in this task.
