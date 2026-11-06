# Proof of positive split-centre quotient L² unfolding

`Langlands.Global.PositiveRealTorus.positiveQuotientL2Unfolding` proves
the unchanged public proposition
`Langlands.Global.PositiveRealTorus.PositiveQuotientL2UnfoldingStatement.{u}`.
The number field `F : Type u` has arbitrary universe. The proof retains
the target's injective, finite-index rational-character restriction,
finite split-torus isomorphism, centrality, affine and locally finite-type
group-scheme assumptions, and right invariance of the actual norm-one
Haar measure.

## Actual counting-measure specialization

Put `N = normOneSubgroup F G` and
`Γ = rationalNormOneSubgroup F G`. The existing
`isDiscrete_rationalNormOneSubgroup` proves discreteness of this actual
subgroup. Closedness follows from `Subgroup.isClosed_of_isDiscrete`.
The proof installs `Countable Γ` through
`LeftCosetSpace.countable_of_isDiscrete`, making `Measure.count`
s-finite, and obtains finiteness of counting measure on compact sets
from `LeftCosetSpace.isFiniteMeasureOnCompacts_count`.

Let `Q = NormOneRationalQuotient F G` and
`ν = normOneRationalQuotientHaarMeasure F G`.
The public theorem `normOneRationalQuotientHaarMeasure_isCompatible`
supplies compatibility for the actual triple
`Measure.count`, `Measure.haar`, and `ν`.
The imported `Langlands.QuotientIntegration.quotientL2Unfolding`
therefore gives continuity and compact support of the actual average

\[
  A_f(\Gamma x)=\int_\Gamma f(\gamma x)\,d\#\gamma
\]

for every `f : C_c(N, ℂ)`. This is the existing `quotientAverage`;
the proof uses the generic theorem's continuity and compact-support
conclusions.

## Positive quotient vector and continuous form

Write `Q+ = PositiveRationalQuotient F G T i`,
`j = normOneToPositiveQuotient F G T i`, and
`μ+ = positiveRationalQuotientHaarMeasure F G T i`.
The existing `positiveQuotientHomeomorph` has forward map `j`.
Composition of `A_f` with its inverse is exactly the existing
`positiveNormOneQuotientAverage`, denoted `A_f+`. Composition transports
continuity and compact support to this actual function.

The proof installs the public Borel, Hausdorff and locally finite measure
instances for `Q+`. Continuity and compact support give
`MemLp A_f+ 2 μ+`. The vector is `v = MemLp.toLp A_f+`, whose chosen
representative agrees with `A_f+` almost everywhere. The continuous
complex-linear form is `ℓ = innerSL ℂ v`, so
`ℓ φ = inner ℂ v φ` for every `φ : Lp ℂ 2 μ+`. The inner product is
conjugate linear in `v` and linear in `φ`.

## Specified-function unfolding and exact integration

For each actual vector `φ : Lp ℂ 2 μ+`, define the function on `Q`
directly by `ψ(q) = φ(j(q))`, using Mathlib's chosen representative of
`φ`. Its strong measurability follows from `Lp.stronglyMeasurable φ`
and `positiveQuotientMeasurableEquiv`. Its `MemLp ψ 2 ν` follows from
`Lp.memLp φ`, `MemLp.comp_measurePreserving` and the public theorem
`measurePreserving_positiveQuotient`.

The imported helper
`Langlands.QuotientIntegration.integrable_compact_quotient_unfolding`
applies to this specified function `ψ`. It gives absolute convergence
and the identity

\[
 \int_N \overline{f(x)}\,\phi(j(\Gamma x))\,dx
 =\int_Q \overline{A_f(q)}\,\psi(q)\,d\nu(q).
\]

Thus the ambient integrand is exactly the target's specified pullback.
No new pullback `Lp` vector is formed or identified pointwise with `ψ`.

The exact pushforward integration formula identifies the quotient
integral with the positive quotient integral:

\[
 \int_{Q^+}\overline{A_f^+(q)}\,\phi(q)\,d\mu^+(q)
 =\int_Q\overline{A_f(q)}\,\psi(q)\,d\nu(q).
\]

This step uses `integral_positiveRationalQuotientHaarMeasure` and
`positiveNormOneQuotientAverage_normOneToPositiveQuotient`.
Finally, `L2.inner_def` and almost-everywhere agreement of `v` with
`A_f+` identify the left side with `inner ℂ v φ`. Together these
equalities give the asserted Hilbert pairing and ambient integral.
The measure remains exactly the existing pushforward `μ+ = j_*ν`;
the proof introduces no rescaling or finite total quotient volume.

## Provenance and scope

This is an internal specialization of the public generic proof and its
specified-function helper, using the public actual adelic subgroup,
quotient-homeomorphism and measure-transport results. It adds no new
assertion about the original literature motivating the target.

Worker 116 authored the Lean proof and its initial explanation in shared
draft revision 37 of task `34b81620-20d7-4059-9b08-6bedd1c1c029`.
Worker 1684 adopted that Lean module unchanged, checked its public
dependencies and expanded this explanation for the focused submission.

The result concerns compact norm-one tests, their positive quotient L²
vectors, continuous forms and absolute unfolding. Full character-period
transforms, test separation, cuspidal closedness, smoothness and spectral
theorems remain separate obligations.
