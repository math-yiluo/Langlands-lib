# Invariant affine covers at a finite level of a cartesian diagram

Author: Worker 706.

This internal construction supplies the invariant-open descent step in Stacks
Lemma 70.5.11, Tag 07SR, used by Proposition 70.8.1, Tag 07SU. The registered
originals are `stacks-stratification-2026-11-02` and
`stacks-noetherian-approximation-2026-11-01`. It combines the already constructed
category of cartesian relation morphisms with Mathlib's scheme limit theorems
for affine transition maps. No quotient or Noetherian first level is assumed
or constructed. The index category and all schemes retain universe `u`.

Work with a cofiltered diagram `D` of étale equivalence relations and a cone
`c` of actual cartesian morphisms whose object-scheme cone is limiting.
`isLimitRelation` proves that its relation-scheme cone is limiting too.
The source maps give a natural transformation, and the source square of each
cone leg is a pullback by cartesianness. Pullbacks commute with connected
limits, so Mathlib's `isLimitOfIsPullbackOfIsConnected` applies.
This construction does not require affineness.

For the remaining descent results, both the object and relation schemes
at every level are affine. In particular, all transition morphisms and
both endpoint morphisms are affine and quasi-compact.

`exists_isInvariantOpen_preimage` starts with an affine open `V` at a
specified level whose inverse image in the limit is invariant. Its source
and target inverse images at that level are compact opens. Endpoint
compatibility identifies their inverse images under the relation cone leg.
Mathlib's `exists_map_preimage_eq_map_preimage` then makes these two opens
equal after a transition. Endpoint compatibility identifies the resulting
equality with invariance of the pulled-back `V`.

`exists_isAffineOpen_isInvariantOpen_preimage_eq` first descends an affine
open of the limit with Mathlib's `exists_isAffineOpen_preimage_eq`. The
preceding result then makes it invariant. Pulling back an affine open under
an affine morphism retains affineness, and the cone equation retains its
prescribed inverse image.

`exists_invariantAffineCover` descends a given finite affine cover with
Mathlib's `Scheme.exists_isOpenCover_and_isAffine_of_finite`, retaining its
indexing type. For each member the preceding equality argument supplies a
later invariance level. `IsCofiltered.wideCospan` gives a single level whose
maps factor all these transitions. Inverse images preserve invariance;
inverse images of the original level cover still cover that common level.
The cone equations retain all the originally prescribed opens.
No nonemptiness assumption on the finite indexing type is added.

`InvariantAffineCoverModel` records the actual index, the opens, their
covering, affineness and invariance, and their inverse-image equations.
`invariantAffineCoverModel` chooses such data from the proved finite-cover
existence theorem. These definitions do not assert that the descended chart
relations have quotients; that is a further affine quotient descent step.
