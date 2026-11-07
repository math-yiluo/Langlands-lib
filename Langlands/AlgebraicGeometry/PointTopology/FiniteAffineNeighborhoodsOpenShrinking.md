# Shrinking finite-set affine neighborhoods inside open subschemes

Author: Worker 1203.

This is an internal scheme-theoretic support unit for finite-surjective AF
descent. Its assertions are derived from the existing
`PointTopology.HasFiniteAffineNeighborhoods` definition, the published
`GenericPointAvoidance.exists_basicOpen_of_finite` theorem, and Mathlib's
open-immersion and quasi-affine APIs. It does not assert descent or
representability of an algebraic space.

`FiniteAffineNeighborhoodsOpenShrinkingStatement.{u}` says that for an
actual scheme `X : Scheme.{u}` satisfying the AF condition, every finite
subset `E` contained in an open `W` has an affine open neighborhood `V`
with `E ⊆ V` and `V ≤ W`. All underlying points are allowed, and `E` may
be empty. Neither `X` nor `W` is assumed quasi-compact.

The implemented proof first chooses an affine open `U` containing `E`.
The inverse image of `E` in `U` is finite because an open immersion is
injective. Prime avoidance on the affine scheme `U` supplies a principal
open containing that inverse image and contained in the inverse image of
`W`. Its image under the inclusion of `U` is the required affine open in
`X`. The theorem `finiteAffineNeighborhoodsOpenShrinking` proves the
stated proposition, and `exists_affineOpen_subset_of_finite` exposes its
direct API.

`hasFiniteAffineNeighborhoods_of_isOpenImmersion` applies this shrinking
result to the finite image set and the open image of an arbitrary open
immersion. Pulling back the resulting affine open proves the AF property
for the source. `hasFiniteAffineNeighborhoods_open` specializes this to
any open subscheme, without a compactness assumption.

Finally, `isQuasiAffine_of_le_affineOpen` proves that a compact open `V`
contained in an affine open `U` is quasi-affine. Its actual inclusion
`X.homOfLE hVU : V.toScheme ⟶ U.toScheme` is an open immersion, and compactness of `V`
provides the compact-space instance required by
`Scheme.IsQuasiAffine.of_isImmersion`. Compactness is required only for
this last conclusion, in accordance with Mathlib's quasi-affine
convention.

The finite-surjective quasi-affine-source representability theorem,
algebraic-space shrinking, scheme gluing and the exact AF-descent target
remain separate proof obligations.
