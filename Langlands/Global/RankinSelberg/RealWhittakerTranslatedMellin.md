# Uniform bounds for compact families of right translates of real Whittaker functions

`alpha g` denotes the logarithmic diagonal Iwasawa coordinate of `g ∈ GL_{n}(ℝ)` (`RealIwasawa`)
and `rootPos y = Σ_i max(y_i - y_{i+1}, 0)` the positive simple-root sum.

## Definitions and results

* `HasGaugeBound W`: there is `N` such that for every `M` there is `C ≥ 0` with
  `‖W g‖ ≤ C exp(-M · rootPos (alpha g) + N Σ_j |alpha g j|)` for all `g`.
* `hasGaugeBound_of_mem_model`: every member of the refined real Whittaker space
  `realUniformWhittakerModel r ds a` has a gauge bound (from `realUniformWhittakerRegularity`,
  the Library's `hasUniformGauge_of_derivativeGrowth` and `HasUniformGauge.any`).
* `alpha_right_mul`: `alpha (x y) = alpha x + alpha (kpart(x) y)`, from the Iwasawa decomposition
  `x = npart(x) · torus(alpha x) · kpart(x)`.
* `compact_rightTranslate_uniformGauge`: if `W` has a gauge bound and `S` is compact, the family
  `s ↦ (g ↦ W(g s))`, `s ∈ S`, has a uniform gauge (`RealUnequalFamily.HasUniformGauge`). The
  displacement `alpha(kpart(g) s)` is bounded uniformly over the orthogonal group and `S`, which
  costs a fixed factor in the growth and simple-root terms.
* `exists_compact_mellin_bounds`: for `W`, `V` with left characters `a`, `-a` and gauge bounds,
  group elements `g`, `g'` and rapidly decreasing weights `f`, `f'`, there are integrable `M`,
  `M'` bounding `weightedOrdinary h (ρ(k g) W) (ρ(l g') V) f` and
  `weightedDual h (ρ(k g) W) (ρ(l g') V) f'` for all orthogonal `k`, `l`. The half-plane
  dominations `ordinary_halfPlaneDomination` and `dual_halfPlaneDomination` of the Library are
  applied to the compact translation families, and each rapidly decreasing weight is bounded by a
  constant times a real power of the determinant in the corresponding half-plane.

This module is the real counterpart of the parts of the Library's
`ComplexWhittakerTranslatedMellin` used by the larger-gap recurrence; it supplies the integrable
bounds needed for `RealWhittakerTranslatedIntegrals`, in the setting of Jacquet, *Archimedean
Rankin–Selberg Integrals* (2009), §10.3.
