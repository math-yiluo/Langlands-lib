# Regular-atlas assembly and the intrinsic family criterion: proof

The theorem

```lean
theorem regularAtlasComparison (k : Type) [RCLike k]
    (X : Over (Spec (CommRingCat.of k))) [IsAffine X.left] (d : ℕ) :
    regularAtlasComparisonStatement.{v, w, z} k X d
```

proves the published proposition `regularAtlasComparisonStatement` with
its three source universes `v`, `w`, `z` as free level parameters. It
covers every `RCLike` coefficient field in `Type`, every affine `X`, and
every `d`. It uses only the fields of the given `RegularAtlas`. It does
not construct an atlas from algebraic smoothness. Both conjuncts follow from
the auxiliary results below, without any case split. For `d = 0` the model
`Fin 0 → k` is a point, and every coordinate condition over `Fin 0` is
vacuous. For an empty `RingPoint k X k` the quantifiers over points, charts
and atlas members are vacuous. The general argument covers both cases
unchanged.

## Smoothness of chart changes

`RegularChart.contDiffOn_transition c c'` proves that
`c.homeomorph.symm ≫ₕ c'.homeomorph` is `ContDiffOn ℝ ∞` on its source,
for any two regular charts. The source is rewritten as
`c.homeomorph.target ∩ c.homeomorph.symm ⁻¹' c'.homeomorph.source`.
Then `contDiffOn_pi` reduces the claim to one coordinate `i`. On that set
the field `c'.apply_eq` shows that coordinate `i` of
`c'.homeomorph (c.homeomorph.symm v)` equals

`regularEvaluation (c.homeomorph.symm v) (c'.numerator i) /
regularEvaluation (c.homeomorph.symm v) (c'.denominator i)`.

The field `c.contDiffOn_inverse_evaluation` gives smoothness of numerator
and denominator on `c.homeomorph.target`, hence on the smaller set.
`c'.denominator_ne_zero` says that the denominator does not vanish there.
The quotient is written as `numerator * denominator⁻¹`. Mathlib's
`ContDiffOn.mul` and `ContDiffOn.inv` apply to `k` as a normed `ℝ`-algebra,
and `ContDiffOn.congr` transfers the result to the transition map.

`RegularAtlas.isManifold A` states
`IsManifold 𝓘(ℝ, Fin d → k) ∞ (RingPoint k X k)` for `A.chartedSpace`. It
applies Mathlib's `isManifold_of_contDiffOn`. Both atlas members lie in the
range of `fun p => (A.chartAt p).homeomorph`, so each is the chart at some
point. For the model `𝓘(ℝ, Fin d → k)`, the model-with-corners maps are the
identity and their range is `univ`. After rewriting with these facts,
`contDiffOn_transition` gives exactly the required condition. This is the
first conjunct, `regularAtlasManifoldStatement`.

## Regular evaluations on the atlas charted space

`RegularAtlas.contMDiff_regularEvaluation A a` proves that
`fun p => regularEvaluation p a` is
`ContMDiff 𝓘(ℝ, Fin d → k) 𝓘(ℝ, k) ∞` for the atlas charted space, for each
global regular function `a`. At a point `p`, `contMDiffAt_iff` requires
continuity, which is `continuous_regularEvaluation`. It also requires
smoothness of the evaluation read in charts. The target chart for `𝓘(ℝ, k)`
is the identity and the model range is `univ`. So the chart condition is
`ContDiffAt ℝ ∞ (fun v => regularEvaluation ((A.chartAt p).homeomorph.symm v) a)`
at `(A.chartAt p).homeomorph p`. This follows from the chart field
`contDiffOn_inverse_evaluation`, because the chart target is open and
contains the image of `p`.

## The family criterion

`RegularAtlas.contMDiff_iff_regularSmooth A I f` proves
`ContMDiff I 𝓘(ℝ, Fin d → k) ∞ f ↔ RegularSmooth I f` for the atlas charted
space. Here `I` is a real model with corners on any normed space `E` and
model space `H`, and `M` is any space with a charted-space structure over
`H`. The universes of `E`, `H` and `M` are arbitrary. This auxiliary result
does not need the source hypothesis `IsManifold I ∞ M`. The main theorem
receives that hypothesis from the target statement and ignores it, which
gives the second conjunct, `regularAtlasFamilyCriterionStatement`.

- Forward. For each global regular function `a`, compose the result of the
  previous section with `f` using `ContMDiff.comp`. Composition needs no
  manifold hypothesis.
- Reverse. Assume `RegularSmooth I f`. First, every function
  `fun t => regularEvaluation (f t) a` is continuous, so `f` is continuous
  by the published criterion `continuous_iff_regularEvaluation`. At a point
  `t`, `contMDiffAt_iff_target` reduces the claim to this continuity and to
  smoothness of `extChartAt 𝓘(ℝ, Fin d → k) (f t) ∘ f`. That map is the
  chart `(A.chartAt (f t)).homeomorph` applied to `f`. `contMDiffAt_pi_space`
  reduces it to each coordinate `i`. The map `q ↦ q.1 * q.2⁻¹` on `k × k`
  is `ContDiffAt ℝ ∞` at the pair of numerator and denominator values at
  `f t`, by `contDiffAt_fst`, `contDiffAt_snd`, `ContDiffAt.inv` and
  `ContDiffAt.mul`. The denominator is nonzero by `denominator_ne_zero` and
  `A.mem_source`. The paired evaluations are `ContMDiffAt` by the
  hypothesis and `ContMDiffAt.prodMk_space`, and `ContDiffAt.comp_contMDiffAt`
  composes the two. By continuity of `f` and openness of the chart source,
  `f s` lies in that source for all `s` near `t`. For such `s`, the chart
  coordinate equals the quotient by the field `apply_eq`.
  `ContMDiffAt.congr_of_eventuallyEq` then transfers smoothness.

## Provenance

The proof is internal. It derives the result from the explicit fields of
`RegularChart` and `RegularAtlas`, the published
`continuous_regularEvaluation` and `continuous_iff_regularEvaluation`, and
Mathlib's manifold and `ContDiff` calculus. It follows the route that the
statement's Markdown and the task context describe. No literature result is
transcribed.
