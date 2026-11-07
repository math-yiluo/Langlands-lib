# Mackey's formula for induction along open embeddings

Worker 1828 derives this auxiliary unit for proof task
`cfea3159-7908-43b1-a677-75834c3859bd`. It restates the Mackey formula of
`Langlands.VirtualRepresentation.ExactMackey` in the shape of condition 2 of
`Langlands.ClassField.Global.RelativeWeilGroup.LocalInducedRestriction`, using the
published `ExactGrothendieckGroup.continuousInduceAlong` of
`Langlands.VirtualRepresentation.Global.RelativeWeilLocalRestrictionStatement`.
That definition is restriction along the inverse of an open embedding onto its
range, followed by induction from the range. The source is Serre (1977), §7.3,
Proposition 22; see the Markdown of `ExactMackey` for how this version differs.

## Declarations and proofs

`continuousRestrict_continuousRestrict`: successive continuous restrictions along
`φ` and then `ψ` equal restriction along `φ.comp ψ`. This is the published
`restrict_comp` applied to an element.

`continuousRestrict_continuousInduceAlong`. Setting:
- `G` and `L` are topological groups in one universe and `M` is a topological
  group.
- `j : M →ₜ* G` is an open embedding with finite-index range, and
  `ι : L →ₜ* G` is continuous.
- For `u` in a finite type `U`: `φ u : N u →ₜ* L` are open embeddings with
  finite-index ranges, `ιu u : N u →ₜ* M` are continuous, and `x u : G`.

Hypotheses:
- `hι`: `j (ιu u n) = x u * ι (φ u n) * (x u)⁻¹`.
- `hS`: if `x u * ι ℓ * (x u)⁻¹` lies in the range of `j`, then `ℓ` lies in the
  range of `φ u`.
- `hcover`: every `g` is `j m * (x u * ι ℓ)`.
- `hdisj`: `j m * (x u * ι ℓ) = j m' * (x u' * ι ℓ')` implies `u = u'`.

Then for every continuous exact virtual representation `y` of `M`:

`continuousRestrict ι (continuousInduceAlong j hj y) = ∑ u, continuousInduceAlong (φ u) (hφ u) (continuousRestrict (ιu u) y)`.

Proof. Take `H` to be the range of `j` and `S u` the range of `φ u`. The
conjugation map `κ u : S u → H` is `s ↦ j (ιu u (φ u⁻¹ s))`, continuous as a
composite with the continuous range inverse `InductionAlong.rangeInverse`. `hι`
gives `κ u s = x u * ι s * (x u)⁻¹`, and `hcover` and `hdisj` translate directly
to the subgroup `H`. The Mackey formula `continuousRestrict_continuousInduce`
then rewrites the left side. Each summand is matched with the right side by
`continuousRestrict_continuousRestrict` and the identity
`j⁻¹ ∘ κ u = ιu u ∘ (φ u)⁻¹` on `S u`. That identity holds because
`rangeInverse j (j m) = m` (`InductionAlong.rangeInverse_apply`).

## Use for the target

For `LocalInducedRestriction c F K E h z (discreteLocalMap ι)`, condition 2 is
this theorem with:
- `j := restrictionInclusion c F E K h` and `hj := isOpenEmbedding_restrictionInclusion c F E K h`;
- `ι := discreteLocalMap ι` and `U := FinitePlacesAbove K z`;
- `N u := localWeilGroup (towerPadicField z u.1)` and `φ u := completionWeilMap z u.1`.

The finite-index instances are the published `range_restrictionInclusion_finiteIndex`
and `completionWeilMap_range_finiteIndex`. The local maps `ιu`, the elements `x u`
and the hypotheses `hι`, `hS`, `hcover` and `hdisj` come from the arithmetic of
places above `z`, which is not part of this unit.

## Public theorems used

`ExactGrothendieckGroup.restrict_comp`, `continuousInduceAlong`,
`InductionAlong.rangeInverse`, `InductionAlong.apply_rangeInverse`,
`InductionAlong.rangeInverse_apply`, `InductionAlong.continuous_rangeInverse`,
`InductionAlong.isOpen_range`, `FiniteRepresentation.isContinuous_restrict`, and
`continuousRestrict_continuousInduce` from `ExactMackey`.
