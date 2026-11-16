# Landing of consecutive block multipliers in arbitrary ambient rank

Module: `Langlands.Representation.Archimedean.RealSwapLandingInStages`.

This is derived infrastructure for the filtration of two induced blocks. It localizes
both proved GL₃ landing statements to three consecutive coordinates in an arbitrary
ambient standard module. Its inputs are the existing induction-in-stages slices and
the proved GL₃ landing theorem; it uses no additional literature or classification result.

Let `pre` and `post` be lists of real blocks, let `a = realRank pre`, and suppose
`a + 3 + realRank post = n`. Write `Φᵖ_k` for `blockFourierCoefficient n p k`, restricted
to `O(n)`. Let `c` be a real character, `d` a complex character of weight `m`, and
`ℓ = |m|`. Put `ε₁ = c.parity.val` and `ε₀ = ℓ + 1 + ε₁`.

`RealSwapLandingInducedFirstInStagesStatement` says the following. Suppose `f` is
`O(n)`-finite in the actual standard module of
`pre ++ [induced d, character c] ++ post`. Let `h` and `u` be continuous functions.
For any complex parameter `δ`, assume `μ₁` is recurrent for `(δ, ε₁)` and symmetric
with sign `(-1)^ε₁`, and `μ₀` is recurrent for `(δ + ℓ, ε₀)` and symmetric with sign
`(-1)^ε₀`. If, on `O(n)`,

- `Φ^(a+1)_k h = μ₁(k) Φ^(a+1)_k f`, and
- `Φ^a_k u = μ₀(k) Φ^a_k h`,

then `Φ^(a+1)_k u = 0` on `O(n)` whenever `|k| < ℓ`.

`RealSwapLandingCharacterFirstInStagesStatement` starts instead with
`pre ++ [character c, induced d] ++ post`, uses `(δ, ε₀)` for `μ₀` and
`(δ + ℓ, ε₁)` for `μ₁`, applies the multipliers first at `a` and then at `a+1`,
and concludes that `Φ^a_k u = 0` on the same forbidden window.

`RealSwapLandingInStagesStatement` is their conjunction. The theorem
`RealSwapLandingInStages.realSwapLandingInStages` proves it unconditionally.
The parameter `δ` is arbitrary and need not be a difference of exponents.
No positivity or nonzero-weight hypothesis is present. The intermediates `h` and
`u` need only be continuous and need not lie in any specified standard module.

The proof uses the slice `σ_κ F(g) = ν(g) F(ι(g) κ)` for each `κ ∈ O(n)`, with
`ι : GL₃(ℝ) → GL_n(ℝ)` embedding the three coordinates starting at `a`.
`InductionStages.slice_mem_kFin` gives membership of the sliced input in the exact
GL₃ standard module, including its `O(3)`-finiteness. The generic helper
`continuous_blockEmb` proves continuity of `ι` from continuity of its matrix and
inverse matrix. `continuous_slice` obtains continuity of `ν` from the already
proved smoothness of the slice of the constant function `1`, and composes with
`F` to handle arbitrary continuous inputs.

`multiplier_slice` transports a compact multiplier identity to the slice by
`InductionStages.blockFourierCoefficient_slice`; the two scalar factors commute.
Apply the corresponding GL₃ landing statement to the three sliced functions.
`blockFourierCoefficient_slice_one` identifies its conclusion at the identity
with the desired ambient coefficient at `κ`, since `ν(1) = 1` and `ι(1) = 1`.
This proves `inducedFirst_of` and `characterFirst_of`; `of_landing` combines them.
The final theorem supplies the proved induced-first analytic landing and its
proved character-first mirror, leaving no landing hypothesis.

This unit proves landing of a two-step multiplier composite. It does not construct
the four-step exchange of two induced blocks or prove its kernel and filtration
properties, and it does not prove `RealInducedInducedFiltrationStatement`.
