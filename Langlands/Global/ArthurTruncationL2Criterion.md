# A criterion for an orthogonal projection extension on L²

**Setting.** `X` is a locally compact, second countable Hausdorff space with its Borel
σ-algebra and a regular measure `m`. The target predicate is
[`IsOrthogonalL2Extension`](ArthurTruncationL2Statement.md): a continuous linear
`IsStarProjection` on `Lp ℂ 2 m` whose value on the class of every measurable, square-integrable
function bounded on compact sets agrees almost everywhere with a given pointwise operator.

**Provenance.** This is the functional-analytic step in the paragraph after the proof of
Arthur 2005, Proposition 13.1 (J. Arthur, *An introduction to the trace formula*, in
`arthur-ellwood-kottwitz-2005-harmonic-analysis-shimura`, printed p. 69, PDF p. 81): "It is not
hard to show from (ii) and (iii) that `Λ^T` extends to an orthogonal projection". Here (ii) is
idempotence and (iii) is the pairing with a continuous compactly supported function. The
module states and proves this step for an abstract operator. The way the projection is
constructed and the almost-everywhere comparison are derived here, since the source gives no
details.

## Auxiliary results

- `integrable_mul_of_isCompact_bound`: a measurable function bounded on compact sets times a
  continuous compactly supported function is integrable. Both factors are bounded on the
  compact topological support of the second, and the product vanishes off it.
- `memLp_two_of_isCompact_bound`: a measurable function that is bounded on a compact set and
  vanishes off it is square integrable. It is essentially bounded and its support has finite
  measure.
- `dense_compactSupport_toLp`: the classes of continuous compactly supported functions are
  dense in `L²(X, m)`. This is Mathlib's approximation
  `MemLp.exists_hasCompactSupport_eLpNorm_sub_le`.
- `ae_eq_zero_of_forall_integral_mul_conj`: a square-integrable `u` with
  `∫ u ψ̄ = 0` for every continuous compactly supported `ψ` vanishes almost everywhere. Its
  class is orthogonal to a dense set.
- `ae_eq_of_forall_integral_mul_conj` (local form): let `g₁` be measurable and bounded on compact
  sets, and let `g₂` be square integrable. If `∫ g₁ ψ̄ = ∫ g₂ ψ̄` for every continuous compactly
  supported `ψ`, then `g₁ = g₂` almost everywhere. Fix a compact set `s` and an Urysohn
  function `η` with values in `[0, 1]`, equal to `1` on `s`, with compact support. Then
  `u = η (g₁ − g₂)` is square integrable. Since `η` is real, `∫ u ψ̄` equals
  `∫ (g₁ − g₂) (ηψ)‾`, which vanishes by hypothesis. So `u = 0` almost everywhere, hence
  `g₁ = g₂` almost everywhere on `s`. A countable exhaustion by compact sets finishes the
  proof.

## The criterion

`isOrthogonalL2Extension_of_pairing` assumes the following of an operator
`Λ : (X → ℂ) → X → ℂ`:

1. for `f` measurable and bounded on compact sets, `Λ f` is measurable and bounded on compact
   sets;
2. `Λ (Λ ψ) = Λ ψ` for every continuous compactly supported `ψ`;
3. for `f` as in 1 and `ψ` as in 2, the function `f · (Λ ψ)‾` is integrable and
   `∫ (Λ f) ψ̄ = ∫ f (Λ ψ)‾`.

It concludes `IsOrthogonalL2Extension m Λ`.

**Proof.** Applying 3 to `Λ ψ` and `ψ` shows that `|Λ ψ|²` is integrable, so `Λ ψ` is square
integrable. Let `S` be the span of the classes `[ψ] − [Λ ψ]` over continuous compactly
supported `ψ`, and let `A` be Mathlib's `Submodule.starProjection` onto the closed subspace
`Sᗮ`. It is a star projection by
`isStarProjection_starProjection`.

- `A [ψ] = [Λ ψ]`. By 3 applied to `Λ ψ` and to `ψ`, and by 2,
  `∫ (Λ ψ) χ̄ = ∫ (Λ ψ)(Λ χ)‾` for all such `ψ, χ`. Hence `[Λ ψ]` is orthogonal to every
  generator `[χ] − [Λ χ]`, so `[Λ ψ] ∈ Sᗮ`. Moreover `[ψ] − [Λ ψ] ∈ S ⊆ Sᗮᗮ`.
- Let `f` be measurable, bounded on compact sets and square integrable. For every continuous
  compactly supported `ψ`,
  `∫ (A[f]) ψ̄ = ⟪[ψ], A[f]⟫ = ⟪A[ψ], [f]⟫ = ⟪[Λ ψ], [f]⟫ = ∫ f (Λ ψ)‾ = ∫ (Λ f) ψ̄`.
  The second equality is the self-adjointness of `A`, and the last is hypothesis 3. By 1,
  `Λ f` is measurable and bounded on compact sets, so the local form above gives
  `A[f] = Λ f` almost everywhere.

The proof does not use linearity of `Λ` and never applies `Λ` to a general `L²` class.
