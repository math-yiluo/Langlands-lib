# The extension of the stable images in one rank

Author: Worker 4803. Module `Langlands.Correspondence.HenniartRankExtension`, namespace
`Langlands.Henniart.Extension`. Universes: `uK` (p-adic fields), `uW` (Weil carriers),
`uV` (supercuspidal carriers), `uE` (local-constant systems), independent. It is a
supporting module of `HenniartSurjectivityStepProof`; it defines no statement.

## Content

Henniart (2000), §4.4, in a single rank `n`. The published module `HenniartExtension`
extends the stable images to all irreducible Weil classes, given stable images in
every rank (`StableCorrespondenceStatement`). This module does the same in one rank,
from `StableExistsAt K n` alone, because the surjectivity step of Henniart's induction
only has stable images in rank `n`.

- `exists_stableDecomposition_of_rank`: if every finite-image unitary class of the
  rank of `b` has a stable image, then `b` has a stable decomposition: `b = z · b₀`
  for a unitary finite-image class `b₀` with stable image `π₀`
  (`IsStableDecomposition`). The proof is that of `exists_stableDecomposition`: the
  published `LocalWeil.unramifiedTwistFiniteFactoring` writes `b = z · b₀`, and
  `b₀` has the rank of `b` because twisting preserves the rank.
- `twist_eq_of_stableDecomposition`: two stable decompositions `(z, π₀)`, `(z', π₀')`
  of one class give `z · π₀ = z' · π₀'`. This is `UnramifiedTwistIndependenceStatement`
  read on generators.
- `eq_of_stableDecomposition`: two stable decompositions with `z · π₀ = z' · π₀'`
  decompose the same class. Here `π₀' = w · π₀` with `w = z'⁻¹ z`, and `‖w‖ = 1`
  because both are unitary (`norm_eq_one_of_unramifiedTwist_unitary`). A candidate
  for both `b₀` and `b₀'` (`exists_common_candidate₂`) is compatible with the twist by
  the unramified field character of value `w` (`candidate_twist_generator`), and it is
  injective, so `b₀' = w · b₀` (`eq_of_candidate`), whence `z · b₀ = z' · b₀'`. This is
  the argument of the published `extensionBasis_injective`.
- `IsStableDecomposition.twist`: a decomposition `(z, b₀, π₀)` of `b` gives the
  decomposition `(w z, b₀, π₀)` of `w · b`.
- `rankExtensionBasis`, `rankExtension`: for `hS : StableExistsAt K n` and `σ` of
  rank `n`, a chosen stable decomposition `σ = z · b₀` is sent to `z · π₀`; the rank is
  `n` (`rankExtensionBasis_rank`), and `rankExtension K hS σ` is the class of rank `n`
  (`sigma_rankExtension`).
- `rankExtensionBasis_eq`: with unramified-twist independence, the value does not
  depend on the decomposition.
- `rankExtension_injective`: with candidate existence and a geometric reciprocity
  candidate `e`, the map is injective (`eq_of_stableDecomposition`).
- `rankExtension_twist`: with unramified-twist independence, the map commutes with the
  twists of Henniart's numerical theorem: `Numerical.weilUnramifiedTwist K k z` on the
  Weil side and `Numerical.supercuspidalUnramifiedTwist K k z` on the side of `GL_(k+1)`.
  The decomposition of `z · σ` is `(z z₀, b₀, π₀)`.

## Provenance

Internal. Henniart (2000), §4.4, printed p. 453 (PDF p. 15): every irreducible `σ` is
`σ₀ χ` with `σ₀` of finite image and `χ` unramified, and `π(σ) = π(σ₀) χ`. The
independence of the choice of `χ` is the published `UnramifiedTwistIndependenceStatement`.
