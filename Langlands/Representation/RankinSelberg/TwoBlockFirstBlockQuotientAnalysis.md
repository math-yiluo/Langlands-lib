# Analytic consequences of first-block quotient disintegration

Module `Langlands.Representation.RankinSelberg.TwoBlockFirstBlockQuotientAnalysis`.
Namespace `Langlands.RankinSelberg.TwoBlockFirstBlockQuotient`.
Author: Worker 117. The analytic organization follows the published helper
`TwoBlockUnipotentQuotientAnalysis` by Worker 235; all group data used here are
the first-block data by Worker 823.

This is an internal helper for the proof of the existing
`TwoBlockFirstBlockQuotientIntegrationStatement`. For an arbitrary canonical
p-adic field and positive two-block shape, it derives the Tonelli law,
absolute-integrability criterion and Bochner law for the published
`firstBlockAverage` from an everywhere kernel representative formula and an
exact composition identity. It constructs no kernel and proves no quotient
measure identity. The normalized measure identity remains an explicit
hypothesis, so this helper alone does not prove JPSS equation (6).

## Objects and hypotheses

The small quotient is `AQ = N_a \ GL_a`, the total quotient is
`HQ = diag(N_a,N_b) \ G`, and the base quotient is
`LQ = diag(GL_a^0,N_b) \ G`. These are exactly the published quotients with
Borel measurable structures. Canonical topologies and local field structures
come from `F.canonicalTopologicalData`; the universe of the field is arbitrary.
There are no representation or character parameters.

Let `νA` be a measure on `AQ`, `hInvariant` its published
`NormOneRightInvariant` property, and `k : ℤ`. A measurable kernel `κ` from
`LQ` to `HQ` is assumed to satisfy, for every representative `g`,

```text
κ [g]_L = map (fun q => fiberPoint q g) (νA.restrict (smallSlice k)).
```

The descent of `firstBlockAverage` uses precisely `hInvariant`; its
pointwise definition is unchanged. For the analytic theorem let `νL0` and
`νHk` be arbitrary measures on `LQ` and `HQ`, and assume
`κ ∘ₘ νL0 = νHk`. In the parent target these are the restriction of the base
measure to the zero determinant slice and the restriction of the total
measure to slice `k`. No scalar or density appears. Neither s-finiteness
nor quotient compatibility is needed for these consequences of an already
measurable kernel; their additional assertions in the parent theorem are
separate obligations.

`FirstBlockKernelAnalysisStatement.{uF}` is a closed `Prop`-valued definition
of the conditional analytic assertion below; `analytic_of_comp_eq` proves it.
The statement includes the representative formula and composition identity as
premises and asserts precisely the analytic consequences, so it does not
assume a proof of the parent target.

## Implemented proof

`firstBlockAverage_eq_integral_kernel` proves the pointwise equality

```text
firstBlockAverage F h νA hInvariant k f = fun q => ∫ z, f z ∂κ q
```

for every measurable complex function `f`, including functions that are not
integrable. Quotient induction reduces to a representative `g`. The published
joint continuity of `fiberPoint` implies continuity of `q ↦ fiberPoint q g`.
The published representative formula for `firstBlockAverage`, the assumed
kernel formula and Mathlib's `integral_map` identify the two total Bochner
integrals. This equality alone makes no convergence assertion.

`analytic_of_comp_eq` proves both analytic conjuncts of the parent target:

1. For every measurable nonnegative extended-real function `f`,
   `∫⁻ q, ∫⁻ z, f z ∂κ q ∂νL0 = ∫⁻ z, f z ∂νHk`.
   Rewrite the composition identity and apply `Measure.lintegral_bind`.
2. For every measurable complex function `f`,
   `Integrable f νHk` is equivalent to almost-everywhere fiber integrability
   together with integrability on the base of the fiber integral of `‖f‖`.
   Rewrite the identity and apply `Measure.integrable_comp_iff` to the
   strongly measurable complex function. This is an absolute-integrability
   criterion, not merely a totalized equality of integrals.
3. If `Integrable f νHk`, then `firstBlockAverage F h νA hInvariant k f` is
   `νL0`-integrable and its integral equals `∫ z, f z ∂νHk`.
   First rewrite the average by the pointwise lemma. Express measure
   composition as composition with a constant kernel from the one-point
   space. Apply `Integrable.integral_comp` for integrability and
   `Kernel.integral_comp` for the Bochner equality. The equality is oriented
   with the total integral on the left, as in the existing target.

## Provenance and limits

The motivating formula is Jacquet, Piatetski-Shapiro and Shalika,
*Rankin–Selberg convolutions* (1983), source ID
`jpss-1983-rankin-selberg`, Section 4.6, printed page 412, equation (6).
The explicit kernel formulation and the integrability criterion are derived
precision of the published target, not separately stated results of JPSS.
This proof uses only the existing first-block objects and Mathlib's general
kernel integration theorems. The normalization of the quotient measures,
existence of the kernel and its s-finiteness, the zero outer slice and the
determinant shift must be established in the other parts of the parent proof.
Equation (7), half-modulus covariance, Fourier or factor identities, and the
distinct unipotent-radical and Section 9.3 towers are outside this helper.

The registered PDF has SHA-256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
Printed page 412, displays (5) and (6), was read visually at zero-based PDF
page 46 (one-based page 47); printed page 411 was also read. No project
errata note for this source was found. The source equation uses the zero
outer slice and the k-th inner slice and gives no separate kernel or
integrability criterion; the distinction between that formula and these
conditional analytic consequences is retained here.
