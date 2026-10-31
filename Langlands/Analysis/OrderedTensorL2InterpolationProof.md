# Proof of L² interpolation for complete ordered derivative tensors

`Langlands.Analysis.orderedTensorL2Interpolation` proves the published
`OrderedTensorL2InterpolationStatement d r` for every dimension `d` and
order `r` (both implicit natural-number arguments). It imports the
unchanged statement module. The proof keeps the statement's
`EuclideanSpace ℝ (Fin d)`, standard basis, canonical `volume`, actual
`iteratedFDeriv` and extended `L²` norms `eLpNorm · 2 volume`. It proves,
for every `k ≤ r`, every real `ε > 0` and every smooth compactly
supported `F`,

`‖TₖF‖₂ ≤ ε^(r-k) ‖TᵣF‖₂ + (ε⁻¹)^k ‖F‖₂`,

with constant exactly one. Here `TₘF(x)` is the statement's square root
of the sum over all ordered words `w : Fin m → Fin d` of
`‖iteratedFDeriv ℝ m F x (e (w 0), …, e (w (m-1)))‖²`. The bound is the
statement's `ENNReal` inequality itself; no norm is projected to the
reals.

## Packed Schwartz tensors and their Fourier transforms

The proof imports the shared helpers from
[`OrderedTensorFourier`](OrderedTensorFourier.md), in the namespace
`Langlands.Analysis.OrderedTensorFourier`. That module contains the unchanged
packing, coordinate evaluation, Fourier postcomposition, extended Plancherel,
ordered derivative multiplier and frequency tensor norm arguments formerly
copied here from the constant-coefficient estimate proof.

## The power inequality and the Schwartz estimate

`scale_power_interpolation` proves, for `k ≤ r`, `ε > 0` and real
`t ≥ 0`,

`t^k ≤ ε^(r-k) t^r + (ε⁻¹)^k`.

If `ε t ≤ 1`, then `t ≤ ε⁻¹`, so `t^k ≤ (ε⁻¹)^k`. Otherwise
`1 ≤ ε t`, so `1 ≤ (ε t)^(r-k)` and
`t^k ≤ (ε t)^(r-k) t^k = ε^(r-k) t^r`, because `(r - k) + k = r`. In
both cases the other summand is nonnegative.

`fourier_orderedTensor_norm` combines the helpers above. For the packed
order-`q` derivative tensor of a scalar Schwartz `f`, the Fourier
transform at `ξ` is the scalar `(2πi)^q 𝓕f(ξ)` times the frequency
tensor. Since `‖2πi‖ = 2π`, its norm is `(2π ‖ξ‖)^q ‖𝓕f(ξ)‖`.

`schwartzOrderedTensorInterpolation` proves the estimate for an actual
Schwartz function `f`, with packed tensors `Tₖ` and `Tᵣ`. Apply the power
inequality at `t = 2π ‖ξ‖` and multiply by `‖𝓕f(ξ)‖`. With the tensor
norm formula at orders `k` and `r` this gives, for every `ξ`,

`‖𝓕Tₖ(ξ)‖ ≤ ε^(r-k) ‖𝓕Tᵣ(ξ)‖ + (ε⁻¹)^k ‖𝓕f(ξ)‖`.

Plancherel rewrites all three `L²` norms as norms of Fourier transforms.
`eLpNorm_mono_real` lifts the pointwise bound. `eLpNorm_add_le` at
`p = 2` is the triangle inequality. `eLpNorm_const_smul` with
`Real.enorm_eq_ofReal` extracts the coefficients `ENNReal.ofReal`.
`eLpNorm_norm` removes the pointwise norms. The factor `2π` is Mathlib's
Fourier normalization. It adds no constant, since the power inequality
holds for every `t ≥ 0`.

## Conversion from smooth compact support

The final theorem converts the given `F` with `ContDiff ℝ ∞ F` and
`HasCompactSupport F` into a Schwartz function by
`HasCompactSupport.toSchwartzMap`. Its pointwise values are definitionally
those of `F`. `SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv`
identifies each iterated line derivative with `iteratedFDeriv ℝ q F x`
evaluated on the ordered basis word. With `packSchwartz_apply` and
`EuclideanSpace.norm_eq`, the norm of the packed tensor at `x` is exactly
the statement's square-root sum. `eLpNorm_norm` passes between the
vector-valued packed tensors and these real-valued functions. The
Schwartz estimate then gives the statement.

## Degenerate cases and scope

The argument has no case split on `d`, `r` or `k`. It assumes no
positive dimension or order, no Fourier hypothesis and no nonvanishing
Fourier value. Empty words, empty products, empty sums and
zero-dimensional Euclidean spaces keep their Mathlib meanings, so
`k = 0`, `k = r`, `r = 0` and `d = 0` are covered by the same proof. The
route is the five-step derivation recorded in the statement's Markdown.
The proof is internal and transcribes no literature proof.

This result proves only the interpolation inequality. It proves no
cutoff estimate, local elliptic estimate, factorial bound, analyticity
or automorphic growth.

Worker 94 wrote the Lean proof and its initial description. Worker 1144
rechecked it against the published statement, expanded this description
and submitted it.
