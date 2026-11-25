# The simple trace formula on sums of tensor test functions, from the simple trace formula

`Langlands.TraceFormula.GeneralLinearTensorSimpleTraceFormulaReduction` proves

`Langlands.TraceFormula.generalLinearTensorSimpleTracePieces_of_simpleTraceFormula :
  GeneralLinearSimpleTraceFormulaStatement.{u} → GeneralLinearRadicalIntegralVanishingStatement.{u} →
    GeneralLinearTensorSimpleTracePiecesStatement.{u}`

and

`Langlands.TraceFormula.generalLinearTensorSimpleTraceFormula_of_simpleTraceFormula :
  GeneralLinearSimpleTraceFormulaStatement.{u} → GeneralLinearRadicalIntegralVanishingStatement.{u} →
    GeneralLinearTensorSimpleTraceFormulaStatement.{u}`.

## Proof of the pieces statement

Let `μ` be the image of `Measure.haar` of `GL_n(𝔸_F)` on `AdelicGL F n`, a left Haar measure. For each
`j`, `CompactSmoothAdelicGLTest.exists_eq_sum_convolution_subgroupIndicator` gives a compact open `K`
fixing `bⱼ` on the left and `aⱼ ⊗ bⱼ = ∑ₗ (αₗ ⊗ 1_K) ⋆_μ (α'ₗ ⊗ bⱼ)`. Read on `GL_n(𝔸_F)`, every pair
`f₁ = αₗ ⊗ 1_K`, `f₂ = α'ₗ ⊗ bⱼ` satisfies the hypotheses of the existing statement at `v`:

- both are tensor tests, hence Hilbert–Schmidt by (1);
- `f₂(x · u · y) = α'ₗ(x_∞ y_∞) · bⱼ(x_f u y_f)` for `u` in the finite factor, so (2) gives the local
  vanishing at `wⱼ` for `f₂`, and `GeneralLinearRadicalIntegralVanishingStatement` turns it into the
  vanishing of the integrals over the unipotent radicals of all proper rational parabolics;
- by `CompactSmoothAdelicGLTest.convolution_tensor_subgroupIndicator` the product `f₁ ⋆ f₂` is
  `bⱼ(g_f)` times an archimedean function, so its support lies over the support of `bⱼ`; if
  `aⱼ ≠ 0`, every such finite point is the finite part of a point of the support of `aⱼ ⊗ bⱼ`, and
  (3) applies; if `aⱼ = 0` the factors `α'ₗ` vanish and the product is `0`.

So each piece satisfies `GeneralLinearSimpleTraceExpansion`. The pieces of all `j` are collected
(`GeneralLinearTraceExpansionSum`, closed under finite sums). Integrated operators are additive in
the weight (`Langlands.Analysis.integratedIsometricAction_sum`), and trace-class operators and their
traces add (`Langlands.Analysis.operatorTrace_finsetSum`, from the Library's `operatorTrace_add`).

## Proof of the single-expansion statement

The pieces statement gives `f = ∑ₖ f₁ₖ ⋆ f₂ₖ` with `R(f)` trace class, `tr R(f) = ∑ₖ tr R(f₁ₖ ⋆ f₂ₖ)` and
every piece satisfying the simple trace formula with its own representatives. Each piece is
continuous with compact support (`Langlands.Analysis.continuous_convolution_compactlySupported`,
`Langlands.Analysis.hasCompactSupport_convolution_compactlySupported`), so
`generalLinearSimpleTraceExpansion_finsetSum` (`GeneralLinearSimpleTraceExpansionMerge`) merges the
expansions into one: the representatives are grouped by class and one is kept in each class; a
piece contributes the term at the kept representative by the transport of the orbital terms along
conjugation (`exists_isCompatible_of_isTwistedConjugate`, `TwistedOrbitalTermInvariance`), or
nothing if its family misses the class, by its covering clause.

## Declarations, in order

- `Langlands.Analysis.integratedIsometricAction_sum`: the integrated operator of a finite sum of
  integrable weights is the sum of the integrated operators.
- `Langlands.Analysis.operatorTrace_finsetSum`: a finite sum of trace-class operators is trace class,
  with trace the sum of the traces.
- `Langlands.Analysis.continuous_convolution_compactlySupported`: for `f₁ f₂ : C_c(G, ℂ)` on a
  topological group and `ν₀` finite on compacts, `g ↦ ∫ f₁(x) f₂(x⁻¹ g) dν₀(x)` is continuous
  (`continuousOn_integral_of_compact_support`, the integrand vanishing for `x ∉ supp f₁`).
- `Langlands.Analysis.hasCompactSupport_convolution_compactlySupported`: on a Hausdorff topological
  group it vanishes outside the compact set `supp f₁ · supp f₂`.
- local instances and the local notation `GLₙ`.
- `GeneralLinearTraceExpansionSum`, `generalLinearTraceExpansionSum_zero`,
  `GeneralLinearTraceExpansionSum.add`, `generalLinearTraceExpansionSum_finsetSum`.
- `generalLinearTensorSimpleTracePieces_of_simpleTraceFormula`.
- `generalLinearTensorSimpleTraceFormula_of_simpleTraceFormula`.
