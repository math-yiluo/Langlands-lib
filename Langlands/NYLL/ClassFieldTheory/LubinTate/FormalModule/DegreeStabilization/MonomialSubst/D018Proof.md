# NYLL M351.018: coefficients of a linearly substituted monomial

This module proves the published Library proposition
`Langlands.NYLL.PortInternal.M351.d018Statement` under the prescribed theorem
name `Langlands.NYLL.PortInternal.M351.d018`. The complete binder list is

```lean
{K : Type u} [Field K] {F : LocalField.{u, v} K}
{π : F.valuationSubring} {σ : Type w}
(q d : σ →₀ ℕ) (c : F.valuationSubring)
```

and the conclusion is `d018Statement (π := π) q d c`. The universes `u`,
`v`, `w` are independent, and no finiteness hypothesis on `σ` or uniformizer
hypothesis on `π` is used. Naming the implicit `π` in the conclusion is
necessary because the explicit arguments do not determine it.

Write `O = F.valuationSubring` and `|d| = d.degree`. The published
`d011 π i = MvPowerSeries.C π * MvPowerSeries.X i` represents `π X_i`.
For arbitrary `q, d : σ →₀ ℕ` and `c ∈ O`, the theorem says that the
coefficient at `q` of the substitution of `X_i ↦ π X_i` in `c X^d` is
`π^|d| c` when `q = d`, and zero otherwise. Zero coefficients, zero
exponents and infinite variable types are included.

## Implemented proof

After unfolding `d018Statement`, the proof follows the original source:

1. Function extensionality, `Pi.smul_apply'` and
   `MvPowerSeries.smul_eq_C_mul` identify the substitution family `d011 π`
   with `Function.const σ π • MvPowerSeries.X`.
2. Rewrite backward by `MvPowerSeries.rescale_eq_subst` and then apply
   `MvPowerSeries.coeff_rescale`. The coefficient becomes
   `(q.prod fun i n ↦ π ^ n) * coeff q (monomial d c)`.
3. Split on `q = d`. In the equal case,
   `MvPowerSeries.coeff_monomial_same` gives `c`; expanding `Finsupp.prod`
   and using `Finset.prod_pow_eq_pow_sum` and `Finsupp.degree_apply`
   turns the factor into `π ^ d.degree`. In the unequal case,
   `MvPowerSeries.coeff_monomial_ne hqd` makes the coefficient zero,
   and `mul_zero` closes the equality.

Only finite supports of exponents enter these products. The local
`Classical.propDecidable` instance matches the source and the published
statement's classical decision of `q = d`. No new helper theorem or
mathematical assumption is introduced.

## Source correspondence and provenance

The original is Naganori Yamaguchi (assisted by OpenAI Codex),
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LubinTate/FormalModule/DegreeStabilization.lean),
commit `fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LubinTate/FormalModule/DegreeStabilization.lean`.
The source-private theorem
`LubinTate.SameUniformizer.coeff_subst_linearInVariableStabilization_monomial`
has its `omit [Fintype σ] in` at line 529, statement at lines 530–536
and proof at lines 537–553. Its linear model is the private definition at
lines 400–403. This port preserves the proof after unfolding the published
target and substituting the published name `d011` for the private model.

The readable snapshot is
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LubinTate/FormalModule/DegreeStabilization.lean`,
whose SHA-256 is
`2f7826dadbd3779d2986fcc42611d26f5da79c097cd0e2bdb6d0e8776c1ee717`.
The registered source is `external-lean-reuse-snapshots-2026-10-21`
(content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`),
with attribution supplement `nyll-classfieldtheory-fbd320cd-supplement`
(content fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).
No patch10 edit affects this source module. The published target's paired
Markdown records the same original-source correspondence.

## Imports and complete adaptations

The sole direct import is
`Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.DegreeStabilization.MonomialSubst.LinearStatements`.
It supplies the exact target and, through its published dependencies, `d011`,
the shared `LocalField` and valuation-subring definitions, and Mathlib's
multivariable substitution, rescaling and coefficient lemmas. No additional
direct Mathlib import is needed. The original module instead imported
`Nyll.ClassFieldTheory.LubinTate.FormalModule.RecursiveCoefficient` and
`Mathlib.RingTheory.MvPowerSeries.Trunc`.

The adaptations are the focused import above; moving the source-private
theorem into the public port namespace as `d018`; stating its conclusion as
the existing `d018Statement (π := π) q d c` and unfolding it; replacing
`linearInVariableStabilization` by `d011` in the proof; opening the qualified
`Langlands.NYLL.LocalFieldTheory.DiscreteValuationField` namespace; and
adding the module documentation and dated modification record. The unused
outer `LubinTate.SameUniformizer` namespace openings and BigOperators scope
are omitted. The section `[Fintype σ]` is not declared, matching the
source theorem's explicit omission of it. The noncomputable section, local
classical instance, universe parameters, binder kinds, order and types
are retained. The target module and all its imports are unchanged.

The original copyright, Apache-2.0 release line and author header are
preserved. Existing `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`
remain unchanged, with SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`,
respectively.
