# The metaplectic group is a covering group of `Sp_{2l}(ℝ)`

**Outside GKT.** This file belongs to the archimedean theory, which Gan–Kudla–Takeda leave out
(preface, p. iv).
The counterparts are GKT Theorem 8.8 and Proposition 8.10 (the topology of the metaplectic group
over a nonarchimedean field). The
declarations are in the name space `Langlands.Theta.Real` (`RealMetaplecticGroup` and its name
space are in `Langlands.Theta`).

The module `Langlands.Theta.Real.Metaplectic.Covering` proves that `proj` is a covering map and
that the group is Hausdorff.

## Content

- `Internal.hasFDerivAt_bigCellSection`: along a differentiable family of matrices `m` through `1`,
  `x ↦ (bigCellSection (m x) f) ∈ L²` is Fréchet differentiable, with derivative assembled from
  `bigCellSectionDeriv` (from the derivatives along curves, `Langlands.hasFDerivAt_of_curves`).
- `RealMetaplecticGroup.eventually_weilSchwartz_eq_bigCellSection`: near `1`, `weilSchwartz g` is
  `bigCellSection (proj g)`. The element constructed over `proj g` with this operator differs from `g`
  by an element of the kernel; if it were `negOne`, `weil g` would be close to `-1` on a fixed vector,
  contradicting continuity.
- `T2Space (RealMetaplecticGroup l)`: the defining map to `Sp × (L² → L²)` is injective.
- `RealMetaplecticGroup.isCoveringMap_proj`: `proj` is open (a local section over the identity is
  `s ↦` the element with operator `bigCellSection s`, continuous by the derivative estimate),
  surjective, with discrete kernel `{1, negOne}`; a quotient map of topological groups with discrete
  kernel is a covering map (Mathlib's `IsQuotientMap.isQuotientCoveringMap_of_isDiscrete_ker_monoidHom`).

## Source and licence

From <https://github.com/leanprover-community/riemann-hypothesis>, commit `f1f6d65`: `src/Development/WeilBound/ThetaLifts/Reductions/MetaplecticDerivatives/HasFDerivAtOfCurves.lean`, lines 59–153 (`hasDerivAt_det_one`, `curve`, `secDer`),
`src/Development/WeilBound/ThetaLifts/Reductions/MetaplecticDerivatives/MetaplecticGroupT2Space.lean` (whole), and `src/Development/WeilBound/ThetaLifts/Reductions/MetaplecticDerivatives/MpFOne.lean`, lines 12–52 (linearity of
`mq`, `vf`, `Qd`). The repository has no licence file; the text is used with attribution, see `licenses/RiemannHypothesis/SOURCE.md`.

## Changes against the source

- Namespaces `PositivityTheory.ThKR.Mp`, `…Mp.MpE`, `…Mp.MpG` → `Langlands.Theta` and
  `Langlands.Theta.Real.Internal`.
- The named propositions are replaced by theorems: `secDer : SecDer l` →
  `hasFDerivAt_bigCellSection` (internal), `nearOne_of` → `eventually_weilSchwartz_eq_bigCellSection`,
  `metaplectic_group_t2Space` → an instance, `cover_of` → `isCoveringMap_proj`; the hypotheses
  `SecEx`, `Ker`, `SecDer`, `TopG`, `Surj` are replaced by the corresponding theorems.
- `hasFDerivAt_of_curves` (lines 10–57) is in `Langlands/Analysis/FDerivOfCurves`.

## Declarations

Public declarations of the file (internal ones are in the namespace `Langlands.Theta.Real.Internal` or
`Langlands.HeisenbergGroup.Internal` and are not listed):

- theorem `Langlands.Theta.RealMetaplecticGroup.eventually_weilSchwartz_eq_bigCellSection`
- instance `Langlands.Theta.RealMetaplecticGroup.instT2Space`
- theorem `Langlands.Theta.RealMetaplecticGroup.isCoveringMap_proj`

## Dependencies

`Langlands.Theta.Real.Metaplectic.BigCell`, `Langlands.Analysis.FDerivOfCurves`.
