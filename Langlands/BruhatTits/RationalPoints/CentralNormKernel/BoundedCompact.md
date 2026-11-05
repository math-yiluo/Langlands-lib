# Closed sets of rational points with bounded matrix entries are compact

Author: Worker 1532.

Namespace: `Langlands.BruhatTits.RationalPoints.CentralNormKernel`. Let `F` be a nonarchimedean
local field with the norm `LocalGalois.localNormedField F`.

- `isCompact_generalLinear_bounded N C`: the set of `g : Langlands.GeneralLinear N F` with
  `‖g k l‖ ≤ C` and `‖g⁻¹ k l‖ ≤ C` for all `k, l` is compact. `F` is a proper space
  (`ProperSpace.of_locallyCompactSpace`), so the set `K₀` of matrices with entries in the closed
  ball of radius `C` is compact (`isCompact_univ_pi`), and so is its image in the opposite ring.
  The set in question is the preimage of `K₀ × K₀ᵐᵒᵖ` under the closed embedding
  `Units.embedProduct` (`Units.isClosedEmbedding_embedProduct`).
- `isCompact_of_isClosed_of_bounded`: let `G` be a group scheme over `Spec F` with `G.X.left`
  affine, `ρ : MatrixRepresentation G (Fin N)` a closed immersion, and `B` a set of rational
  points, closed in `rationalPointTopology F G.X`, such that the entries of `ρ(g)` and of
  `ρ(g)⁻¹` are bounded by `C` for all `g ∈ B`. Then `B` is compact. The map `g ↦ ρ(g)` is a closed
  embedding into `GL_N(F)`: the published `isClosedEmbedding_rationalPointMap` for the closed
  immersion `ρ`, followed by the published homeomorphism
  `GeneralLinear.rationalPointsContinuousMulEquiv`, whose values are the matrices
  `ρ.rationalMatrix g` (`rationalPointsEquiv_apply_apply`, `rationalMatrix_apply_apply`). The
  image of `B` is a closed subset of the compact set above, and an inducing map reflects
  compactness.
