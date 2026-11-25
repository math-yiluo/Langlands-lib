# Hilbert–Schmidt integral operators have square-integrable kernels

Module `Langlands.Analysis.HilbertSchmidtIntegralKernel`, namespace
`Langlands.Analysis.OperatorIdeals`.

A Hilbert–Schmidt operator on `L²(X, μ)` that is given by a kernel whose rows are square
integrable has a kernel in `L²(X × X, μ × μ)`. The kernel is the given one, not a kernel produced
by the abstract theory. The trace-class integral operators to which
`TraceClassContinuousKernelDiagonalStatement` (module
`Langlands.Analysis.TraceClassKernelDiagonalStatement`) is applied are often given in this form, and
that statement asks for the `L²` membership of the kernel.

## Statements

- `countable_of_hilbertBasis`: for `ι 𝕜 E : Type*` with `[RCLike 𝕜] [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E] [TopologicalSpace.SeparableSpace E]` and `b : HilbertBasis ι 𝕜 E`,

  `Countable ι`.

- `memLp_uncurry_of_isHilbertSchmidt`: for `X : Type*` with `[MeasurableSpace X]
  [MeasurableSpace.CountablyGenerated X]`, `μ : Measure X` with `[SFinite μ]`,
  `T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ`, `hT : IsHilbertSchmidt T`, `K : X → X → ℂ` and

  - `hKm : AEStronglyMeasurable (Function.uncurry K) (μ.prod μ)`,
  - `hrow : ∀ᵐ x ∂μ, MemLp (K x) 2 μ`,
  - `hTK : ∀ φ : Lp ℂ 2 μ, (T φ : X → ℂ) =ᵐ[μ] fun x => ∫ y, K x y * φ y ∂μ`,

  the conclusion is

  `MemLp (Function.uncurry K) 2 (μ.prod μ)`.

  In words: on a countably generated measurable space with an s-finite measure, if a
  Hilbert–Schmidt operator `T` acts by `(T φ)(x) = ∫ K(x, y) φ(y) dμ(y)` almost everywhere, with
  `K` almost everywhere strongly measurable on `X × X` and `K(x, ·) ∈ L²(μ)` for almost every
  `x`, then `K ∈ L²(X × X, μ × μ)`.

`IsHilbertSchmidt` is the Library's predicate (module `Langlands.Analysis.OperatorIdeals`): square
summability of `‖T (b i)‖` on one Hilbert basis `b`. `MemLp f 2 μ` is Mathlib's
`eLpNorm f 2 μ < ∞`. Here `eLpNorm` is `∞` for a function that is not almost everywhere strongly
measurable, which is why `hKm` is a hypothesis.

## Proofs

- `countable_of_hilbertBasis`: distinct basis vectors satisfy `‖b i - b j‖² = 2`, so the open
  balls of radius `1 / 2` about them are pairwise disjoint. In a separable space a family of
  pairwise disjoint nonempty open sets is countable (`Pairwise.countable_of_isOpen_disjoint`).
- `memLp_uncurry_of_isHilbertSchmidt`: let `b` be the Hilbert basis given by `hT`, with
  `Σ_i ‖T (b i)‖² < ∞`. The space `L²(μ)` is second countable (Mathlib's `Lp.SecondCountableTopology`
  for a countably generated σ-algebra and an s-finite measure), so the index set of `b` is countable.
  Hence there is one null set off which, for every `i`, `(T (b i))(x) = ∫ K(x, y) (b i)(y) dμ(y)` and
  `K(x, ·) ∈ L²(μ)`. For such `x` let `r_x ∈ L²(μ)` be the class of `conj K(x, ·)`. Then
  `⟪r_x, b i⟫ = (T (b i))(x)`. Parseval's identity (`HilbertBasis.hasSum_inner_mul_inner`, real
  parts) gives `∫ |K(x, y)|² dμ(y) = ‖r_x‖² = Σ_i |(T (b i))(x)|²`. Tonelli's theorem on `μ × μ`
  (`lintegral_prod`) and the monotone convergence theorem for series (`lintegral_tsum`) give

  `∫∫ |K|² d(μ × μ) = ∫ Σ_i |(T (b i))(x)|² dμ(x) = Σ_i ‖T (b i)‖² < ∞`,

  all in `ℝ≥0∞`. By `eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top` this is `MemLp`.

The argument uses only the Hilbert basis supplied by `IsHilbertSchmidt`, so no basis independence
is needed. It does not use the general fact that a Hilbert–Schmidt operator has an `L²` kernel, nor
uniqueness of kernels.

## Declarations, in order

- `countable_of_hilbertBasis`
- `lintegral_enorm_sq_L2` (private): `∫⁻ x, ‖g x‖ₑ ^ 2 ∂μ = ENNReal.ofReal (‖g‖ ^ 2)` for
  `g : Lp ℂ 2 μ`.
- `memLp_uncurry_of_isHilbertSchmidt`

## Literature

C. Brislawn, *Traceable integral kernels on countably generated measure spaces*, Pacific J. Math.
150 (1991), 229–240, printed p. 230, (1.3): "every Hilbert–Schmidt operator, `K`, on `L²(X)` is given
by an integral kernel `K(x, y) ∈ L²(X × X, μ × μ)`". Brislawn states this without proof. The module
proves the part of it that is needed when a kernel with square-integrable rows is already given: that
kernel is itself in `L²(X × X)`.
