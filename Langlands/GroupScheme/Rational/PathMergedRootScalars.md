# Nonzero merged-root scalars on normalized path lines

This internal prerequisite derives the nonzero normalized-basis coefficient of any supplied parametrization of the sum of two adjacent simple path roots. It uses the intrinsic comparison of root parametrizations from `RootParametrizationScalars`, the general positive-root matrix and action formulas from `PathPositiveRootMatrices`, and the published conjugated root-map construction from `AdjacentModifiedData`. It is derived infrastructure; no direct literature assertion is claimed.

The data are an arbitrary field `k : Type u`, an actual affine group scheme with a supplied split pinning, a finite decidable representation index in `Type`, and a supplied highest-weight representation whose highest weight is fundamental at the first vertex of a supplied path component. A normalized simple-root family and a nonzero initial weight vector determine the normalized path basis. The two adjacent vertices have indices `i` and `i + 1`, where `i + 2 ≤ L`; a supplied root index `α` has root equal to their sum. No parity condition is needed for this prerequisite.

`conjugate_rationalPoint` identifies rational values of the published conjugated root map with actual conjugates in the group. `adjacentRoot_eq_pathWeight_sub` telescopes the two adjacent simple roots to the weight difference `ε_i - ε_(i+2)`.

`canonicalAdjacentRootMap` conjugates the second normalized simple-root map by the first canonical reflection representative, using the adjacent Cartan pairing `-1` to identify its root with `α`. Its action on normalized vector `v_(i+2)` is exactly

`v_(i+2) + c • v_i`.

To prove the action, the first reflection and its inverse fix `v_(i+2)`. The second root point sends that vector to `v_(i+2) + c • v_(i+1)`. The first reflection fixes the first summand and sends `v_(i+1)` to `v_i`. This computes the conjugated action with its exact scalar and sign.

For any supplied parametrization `z` of `α`, `pathRootScalar_adjacent_ne_zero` compares `z` with this canonical conjugated map using the nonzero scalar from `RootParametrizationScalars`. At coordinate one, both descriptions of the action on `v_(i+2)` agree. Applying the `i`-th coordinate of the normalized path basis identifies `pathRootScalar z i (i+2)` with that comparison scalar, hence proves it nonzero in the original field. The argument holds over finite and imperfect fields and in every characteristic.

This unit supplies merged-root coefficient nonvanishing. Merged representative matrices, modified-product characteristic polynomials and the canonical class-quotient cross-section remain further obligations.
