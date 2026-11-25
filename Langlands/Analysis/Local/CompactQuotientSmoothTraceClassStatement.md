# Trace class of smooth compactly supported weights on a compact quotient (statements)

`Langlands.Analysis.Local.CompactQuotientSmoothTraceClassStatement` contains two proposition
definitions and no proof, in the namespace `Langlands.QuotientIntegration`. They are proved from
`CompactQuotientConvolutionTraceClassStatement` in
`Langlands.Analysis.Local.CompactQuotientSmoothTraceClassReduction`.

## `CompactQuotientSmoothTraceClassStatement`

The setting is that of `CompactQuotientConvolutionTraceClassStatement` (a closed subgroup `H` of
`G` with compact `H \ G`, compatible measures `μG`, `μH`, `ν`, and the right regular action `π` of
`G` on `L²(H \ G, ν)` supplied with its defining property), with these changes:

- `G` is a Lie group modelled on a real normed space `E` (`[ChartedSpace E G]`,
  `[LieGroup 𝓘(ℝ, E) ∞ G]`, Hausdorff, locally compact) with a closed linear realization
  `ρ : G →* 𝔸ˣ` (`Langlands.LinearLieGroup.IsClosedLinearRealization 𝓘(ℝ, E) ρ`) in a
  finite-dimensional normed real algebra `𝔸`; second countability of `G` follows from it and is not
  assumed;
- `μG` is a left Haar measure (`[μG.IsHaarMeasure]`, which contains the finiteness on compact sets
  and the left invariance assumed there).

Conclusion: for every `f : Langlands.Archimedean.smoothCompactKernels E G` there is
`h : Integrable f.val μG` with `IsTraceClass (integratedIsometricAction μG π hπnorm hπmeas f.val h)`.
The existing statement asks this for convolutions `f₁ ⋆ f₂` of continuous compactly supported
functions; by the Dixmier–Malliavin theorem every smooth compactly supported function is a finite
sum of such convolutions.

## `CompactQuotientProductSmoothTraceClassStatement`

The same on `A × B`, with `A` a Lie group with a closed linear realization as above and `B` a
locally compact, Hausdorff, second countable group, the measurable structure of `A × B` being the
product of the Borel structures. The weights are the `f : C_c(A × B, ℂ)` whose slices
`a ↦ f (a, b)` are smooth and which are right invariant under a compact open subgroup `V` of `B`
(`f (x * (1, v)) = f x`), as in
`Langlands.Analysis.DixmierMalliavin.exists_eq_sum_convolutionIntegral_prod`.

## Source

J. R. Getz and H. Hahn, *An introduction to automorphic representations* (2024), §4.2,
Theorem 4.2.9 (Dixmier–Malliavin lemma), p. 110, as cited on the page of
`CompactQuotientConvolutionTraceClassStatement`. Getz and Hahn state it for `G(F)` with `G` an affine
algebraic group over an archimedean local field `F`; here it is used for a Lie group with a closed
linear realization and, in the second statement, on `A × B`. The reduction to convolutions is
the theorem of Dixmier and Malliavin (*Factorisations de fonctions et de vecteurs indéfiniment
différentiables*, Bull. Sci. Math. (2) 102 (1978), §3, Theorem 3.1, p. 6 of the English translation
*Factorizations of infinitely differentiable functions and smooth vectors*, typeset in LaTeX,
translator not named, paginated 1–24, which does not give the pages of the original). Their
Theorem 3.1 holds for any Lie group and gives smooth compactly supported factors.
