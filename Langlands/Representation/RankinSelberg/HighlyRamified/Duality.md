# Inverse transpose and the inverse additive character

Module `Langlands.Representation.RankinSelberg.HighlyRamified.Duality`.

This module supports the proof of
`Langlands.RankinSelberg.HighlyRamifiedGammaStabilityStatement`. A gamma factor is
built from the `L`-polynomial of a pair, its epsilon factor, and the `L`-polynomial
of the dual pair. The dual pair is `(inverseTransposePullback π,
inverseTransposePullback σ)` with the additive character `ψ.scale (-1)`, that is,
`ψ⁻¹` (`symmetricGammaExpression`). This module shows that the hypotheses of
`UniformRankOneTwistStatement` pass from a pair to its dual pair.

## Provenance

These are standard facts. Inverse transpose `g ↦ ᵗg⁻¹` is a continuous
automorphism of `GL_(n+1)(F)` that preserves `GL_(n+1)(O)` and its principal
congruence subgroups. Together with the long Weyl element, it exchanges the
Whittaker characters of `ψ` and `ψ⁻¹`. The Library already provides this exchange
as `dualFunctionalEquiv`. The formal derivations in this module are internal to
this project.

## Lemmas

All statements use the canonical topological data `F.canonicalTopologicalData`
of the p-adic field `F`.

- `isGeneric_inverseTransposePullback F ψ π hπ`: if `π` is generic for `ψ`, then
  `inverseTransposePullback π` is generic for `ψ.scale (-1)`. Irreducibility
  passes along the group automorphism
  (`CuspidalSupport.isIrreducible_comp_mulEquiv_iff`), and so does admissibility
  (`isAdmissible_comp_continuousMulEquiv`). A nonzero Whittaker functional for
  `ψ` maps to a nonzero functional for the inverse standard character under the
  linear equivalence `dualFunctionalEquiv`. The inverse standard character is the
  standard character of `ψ.scale (-1)` (`standardCharacter_scale_neg_one`).
- `inverseTranspose_mem_principalLevelSubgroup F hg`: inverse transpose maps the
  principal congruence subgroup `Conductor.principalLevelSubgroup F r m` into
  itself. If `g` is the image of an integral matrix `h ≡ 1 (mod 𝔪^m)`, then
  `ᵗg⁻¹` is the image of `ᵗh⁻¹`, and `h⁻¹ ≡ 1 (mod 𝔪^m)` entrywise.
- `hasPrincipalLevelVector_inverseTransposePullback F π h`: a nonzero vector of
  `π` fixed by `principalLevelSubgroup F r m` is fixed by the same subgroup under
  `inverseTransposePullback π`, by the previous lemma.
- `additiveConductor_scale_neg_one F ψ`: `ψ.scale (-1)` has the same conductor
  exponent as `ψ`, by `additiveConductor_scale`, since `ord(-1) = 0`.
- `multiplicativeConductor_inv F η`: `a(η⁻¹) = a(η)`. A character is trivial on
  the units of a level exactly when its inverse is.

## Definitions

- `inverseTransposePullbackTwistEquiv F π χ`: the identity map is an equivalence
  from `inverseTransposePullback (π ⊗ χ ∘ det)` to
  `(inverseTransposePullback π) ⊗ χ⁻¹ ∘ det`, because
  `det(ᵗg⁻¹) = det(g)⁻¹` (`RankOneGammaTwist.determinant_inverseTranspose`).
- `inverseTransposePullbackTrivialEquiv F`: the identity map is an equivalence
  from `inverseTransposePullback (rankOneCharacter 1)` to `rankOneCharacter 1`.
  Both act trivially.

The self-dual measure for `ψ.scale (-1)` is the Library's
`DominantRankTransport.negatedSelfDualHaar F ψ ν`. It has the same underlying
measure as `ν`.
