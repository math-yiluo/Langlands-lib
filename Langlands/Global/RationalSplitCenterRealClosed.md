# Closed ambient image of actual positive real torus points

Author: Worker 112.

This internal construction combines the published actual real-to-adelic
comparison with the published closed-immersion theorem on actual adelic
points. It identifies the real model of a supplied rational split torus
with its existing ambient closed image subgroup. No new assertion from
the automorphic literature is attributed to this module.

Let `G` be an affine group scheme over `Spec ℚ`, and let `T` be an affine
commutative group scheme over the same base. Supply an actual group-scheme
map `i : T.toGrp ⟶ G` whose underlying scheme map is a closed immersion,
a finite index type `I : Type`, and a splitting
`e : T.toGrp ≅ splitTorus (Spec ℚ) I`. All rational specializations use
universe zero. The finite index type can be empty, so rank zero is included.
The point topologies are the existing regular-function evaluation
topologies, and subgroup topologies are their induced subtype topologies.

## Closed embedding and the real component

`isClosedEmbedding_ambientRealPositive` proves that the existing continuous
homomorphism `ambientRealPositive G T i` is a closed embedding. Its domain
is `orderedCoefficientPositiveSubgroup ℚ T ℝ`, defined by positivity of
every actual rational character on actual real points. Its target is
the existing actual adelic point group `AdelicGroupPoints ℚ G`.

The proof composes the published closed embedding `realToAdelic T`,
under the supplied splitting, with the published closed embedding
`AdelicGroupPoints.map ℚ T.toGrp G i`, under the supplied closed immersion.
This composite is definitionally the existing ambient map.

`isClosed_ambient_full_image_connectedComponent_one` states that the set
image of the actual real identity component under
`a ↦ RationalRealAdelicPoints.full G (pointMap ℚ T.toGrp G ℝ i a)`
is closed in the ambient adelic group. The proof rewrites this set as
the published intrinsic positive image `imageSubgroup ℚ T G i` using
`ambient_full_image_connectedComponent_one`, then applies its published
ambient closedness theorem.

## Continuous group equivalence to the existing closed subgroup

`ambientRealPositiveEquiv G T i I e` is a continuous group equivalence
from `orderedCoefficientPositiveSubgroup ℚ T ℝ` to
`closedImageSubgroup ℚ G T i`. The target is the existing closed subgroup
whose underlying group is `imageSubgroup ℚ T G i`; no closure or replacement
image is introduced.

The map is the existing ambient map with codomain restricted to this
subgroup. Its injectivity follows from the closed embedding. Its
surjectivity follows from the published range equality
`range_ambientRealPositive`, which uses the supplied finite splitting.
These prove a group equivalence. Forward continuity follows by subtype
restriction. For inverse continuity, the induced-topology property of
the ambient embedding reduces the goal to continuity of its composite
with the inverse. The inverse identity identifies that composite with
the target's subtype inclusion, which is continuous.

`ambientRealPositiveEquiv_apply` states that the forward map on underlying
adelic points is exactly `ambientRealPositive G T i`.
`ambientRealPositiveEquiv_apply_eq_full` gives the actual real-point formula
above, with the finite adelic point equal to the identity.
`ambientRealPositiveEquiv_symm_apply` states that the recovered actual
positive real point maps back to the original ambient subgroup element.

## Scope

No centrality, connected reductivity, finite-type condition on the group
schemes, character-restriction injectivity or finite-index condition is
required. The actual closed immersion and supplied finite splitting remain
explicit hypotheses.

This module takes a rational torus and its ambient closed immersion as
inputs. Restriction of scalars for a general number-field group and the
greatest rational split central torus in Getz–Hahn (2.20) remain separate
obligations. It supplies no closedness result for the positive-times-principal
rational subgroup, quotient measure, reduction theorem or finite volume.
