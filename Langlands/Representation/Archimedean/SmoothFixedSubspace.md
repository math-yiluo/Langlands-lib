# Genuine smooth vectors at a commuting fixed level

This module is internal infrastructure for the proof of
`CuspidalOperatorMultiplicityOneStatement`. It specializes the companion `SmoothInvariantSubspace` to the full subspace
of vectors fixed by a subgroup under a second, commuting bounded action. The entry
declaration is `fixedDerivativeEquiv`. All declarations are in the namespace
`Langlands.Archimedean.SmoothInvariantSubspace`.

## The full fixed subspace

The data are an arbitrary group `L`, a complex inner product space `E`, a supplied
homomorphism `σ : L →* (E →L[ℂ] E)` into bounded operators, and a subgroup
`J : Subgroup L`. No topology on `L` is used, and no compactness or openness of `J`.

`fixedSubspace σ J` is an abbreviation for the existing Library definition
`Langlands.fixedVectors`. It is applied to the algebraic representation obtained by
forgetting continuity, `ContinuousLinearMap.toLinearMapRingHom.toMonoidHom.comp σ`.
No new notion of fixed vector is introduced. `mem_fixedSubspace_iff` unfolds
membership to `∀ j : J, σ (j : L) v = v`.

- `isClosed_fixedSubspace`: the fixed subspace is the intersection over `j : J` of the
  equalizers `{v | σ j v = v}`. Each `σ j` is continuous, so each equalizer is closed,
  and an intersection of closed sets is closed.
- `fixedSubspace_completeSpace` is an instance: when `E` is complete, the closed
  subspace is complete. This instance supplies `[CompleteSpace U]` to the companion's
  results.

The published `Langlands.TensorHilbertHeckeAux.fixedVectors_isClosed` proves a
related closedness. It derives continuity from a norm-preservation hypothesis
`‖τ g x‖ = ‖x‖` on an algebraic representation. Here boundedness is part of the data,
so no norm preservation is needed.

## The commuting Lie-group action

A second group `G` acts by `π : G →* (E →L[ℂ] E)`. The commutation hypothesis is
`hcomm : ∀ g l v, π g (σ l v) = σ l (π g v)`, that is, every `π g` commutes with every
`σ l`.

- `fixedSubspace_invariant`: `π g` preserves the fixed subspace. If `σ j v = v` for all
  `j : J`, then `σ j (π g v) = π g (σ j v) = π g v`.
- `fixedRestriction σ J π hcomm` is the companion's `restriction` of `π` to the full
  `J`-fixed subspace, using this invariance. It is the restriction to the whole closed
  fixed subspace, not to any algebraic or dense carrier. `fixedRestriction_apply` is the
  ambient agreement `(fixedRestriction σ J π hcomm g v : E) = π g v`.
- `isometry_fixedRestriction` and `isContinuousRepresentation_fixedRestriction` pass a
  supplied isometry or joint-continuity hypothesis on `π` to the fixed level. They
  specialize the companion's transfer lemmas.

## Specialized identifications

From here on the model `I`, a charted space structure on `G` and `[CompleteSpace E]`
are assumed. `[LieGroup I ∞ G]` is assumed from the derivative topology onward.

- `isSmoothVector_fixedRestriction_iff`: a fixed vector is smooth for
  `fixedRestriction` exactly when it is smooth for `π`. This is the companion's
  `isSmoothVector_iff`, which uses bounded inclusion and orthogonal projection. Neither
  unitarity nor continuity of `π` is assumed.
- `ambientFixedSmoothSubspace σ J π I` abbreviates the companion's
  `ambientSmoothSubspace π (fixedSubspace σ J) I`. It is the submodule of the ambient
  derivative-topology smooth vectors `DerivativeSmoothVectors I π` whose underlying
  vectors are `J`-fixed. `mem_ambientFixedSmoothSubspace` states this membership
  explicitly. `isClosed_ambientFixedSmoothSubspace` shows that the submodule is closed,
  using `isClosed_fixedSubspace` and the continuous empty-word coordinate. Its proof
  does not use completeness of `E`.
- `fixedDerivativeEquiv` is a continuous linear equivalence from
  `DerivativeSmoothVectors I (fixedRestriction σ J π hcomm)` onto
  `ambientFixedSmoothSubspace σ J π I`. Both sides carry the genuine derivative
  topology of `SmoothDerivativeTopology`. It is the companion's `derivativeEquiv`.
  `coe_fixedDerivativeEquiv_apply` records that it is computed by the companion's
  `derivativeInclusion`.
- `isClosedEmbedding_fixedDerivativeInclusion`: that inclusion, from the fixed-level
  derivative smooth space into the ambient one, is a closed embedding.
  `range_fixedDerivativeInclusion` states that its range is exactly
  `ambientFixedSmoothSubspace σ J π I`.

These identifications use the genuine orbit derivatives `lieDerivative` and their words,
not formal operators.

## Provenance and scope

This is internal generic fixed-level infrastructure, derived from the companion
module, the published `Langlands.fixedVectors`, and the published smooth-vector and
derivative-topology constructions. The universes of the model vector space, model
space, Lie group, Hilbert carrier and second group are independent.

The commuting actions and the subgroup are supplied hypotheses. The module identifies
no actual cuspidal or adelic action. It proves no approximation or density statement
for compact-finite vectors in the derivative topology and no Whittaker extension. It
proves no multiplicity-one theorem.
