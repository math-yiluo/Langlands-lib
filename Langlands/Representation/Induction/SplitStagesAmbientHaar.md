# Ambient subgroup moduli in split induction in stages

This internal construction by Worker 184 identifies the groups used by the
split-kernel compact integral with their original ambient subgroups. It computes
the integral's existing Haar ratio from those identifications. The statements
are derived from the published split-stage and closed-normalizer constructions;
they are not a new source formulation of the geometric lemma.

Let `A` be a group, let `Q`, `L`, `U` be subgroups, and let
`d : IsSemidirectDecomposition Q L U`. Write `r = d.projection`,
`s = Subgroup.inclusion d.levi_le`. Let `P` be any subgroup of `Q` containing
`r.ker`. The existing `splitStagesRetraction` restricts `r` to `P` with target
`LP = P.comap s`. Denote its kernel by `N`. For any ambient subgroup `F`, set
`H = (Q ⊓ F).subgroupOf Q`, `HP = H.subgroupOf P`, and
`D = HP.comap N.subtype`. All subgroup types carry their induced topology.

`splitStagesAmbientKernelEquiv` is the continuous multiplicative equivalence
`N ≃ₜ* U`. It composes `splitStagesKernelContinuousEquiv` with
`CorrectedFiltration.projectionKerEquiv`. Its application theorem says that its
value, viewed in `A`, is exactly the original element of `N` with the nested
subtype wrappers removed. `splitStagesAmbientIntersectionEquiv` restricts this
identification to `D ≃ₜ* (U ⊓ F)`. Its inverse also retains the same ambient
point. These constructions require a topology on `A`, but no topological-group,
closedness, continuity-of-projection, or local-compactness assumption.

`splitStagesAmbient_normalizes` is purely algebraic: `L ⊓ F` normalizes
`U ⊓ F`. The proof uses the semidirect decomposition's Levi-normalizes-radical
property and the fact that a subgroup normalizes itself, followed by the
normalizer-of-intersection inclusion.

For the Haar calculation, assume `A` is a locally compact topological group,
`U` and `F` are closed, `N` is locally compact, and `N` and `D` have specified
measurable spaces satisfying `BorelSpace`. Assume also that `HP` is closed in
`P` and that the section of every element of `LP` lies in `H`. Closedness of
`HP` supplies local compactness of `D` inside `N`. The measurable structures on
`N` and `D` are the supplied ones, not replacements chosen for the calculation.
The ambient closed-subgroup characters use the Borel structures provided by
`HaarModulus`.

For `l : LP`, `splitStagesAmbientHaarRatio_apply` proves

```
splitKernelHaarRatio rP sP HP hsH hHP l
  = delta_U(l) / delta_(U intersect F)(l).
```

Here `rP` is the restricted retraction, `sP` its Levi section,
`delta_U` is `HaarModulus.closedRestrictCharacter U hU L d.levi_le_normalizer`,
and the second character is `closedNormalizerCharacter` for `U ⊓ F`, evaluated
at the same ambient Levi point. Section containment puts that point in `L ⊓ F`
and hence in the intersection normalizer.

The implementation computes the two factors separately. The existing
`splitKernelConjugation` is inverse conjugation by the section, so transport
through the kernel equivalence identifies its Haar character with
`delta_U(l)⁻¹`. Transport through the intersection equivalence identifies the
intersection factor with `delta_(U intersect F)(l)⁻¹`. Both equalities use
`CorrectedFiltration.mulEquivHaarChar_eq_closedNormalizerCharacter`. The defining
ratio is intersection factor divided by kernel factor, so `inv_div_inv` gives
the displayed orientation. Equality of positive units follows from equality of
their values.

The direct imports are `SplitStagesComparison` and `CorrectedOrbitJacquet`.
The former supplies the restricted retraction and split-kernel Haar ratio; the
latter supplies the ambient projection-kernel equivalence and Haar-conjugacy
comparison. This unit neither selects quotient measures nor constructs a new
representation equivalence. It is an ambient-character prerequisite for the
actual rational-point specialization.
