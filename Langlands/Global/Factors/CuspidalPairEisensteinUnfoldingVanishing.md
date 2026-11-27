# Vanishing by Weil averaging

Module `Langlands.Global.Factors.CuspidalPairEisensteinUnfoldingVanishing` (namespace
`Langlands.Global.CuspidalPairEisenstein.Unfolding`) proves an abstract vanishing criterion. It
is used to show that the non-open cells contribute nothing to the generic coefficient of the
Eisenstein series.

## Setting

`H` is a group with a σ-algebra for which multiplication `H × H → H` and inversion are
measurable, and `μ` is a left invariant s-finite measure on `H`. `N ≤ H` is a subgroup, and
`Λ ≤ N` is countable. `ν` is an s-finite measure on `N` that is left invariant, right invariant
and inversion invariant (`setIntegral_mul_right_eq` does not use the inversion invariance).
`sH ⊆ H` and `sN ⊆ N` are measurable strict fundamental domains for left multiplication by
`Λ`: every orbit meets them exactly once.

## Results

- `setIntegral_mul_right_eq`: for `v₀ ∈ N` and a left `Λ`-invariant `G : N → ℂ`,
  `∫_{sN} G(n v₀) dν = ∫_{sN} G(n) dν`. Right translation by `v₀` preserves `ν` and carries
  `sN` to another fundamental domain of `Λ`, and integrals of `Λ`-invariant functions over two
  fundamental domains agree (Mathlib's `IsFundamentalDomain.setIntegral_eq`).
- `setIntegral_eq_zero_of_mul_right` (**vanishing by Weil averaging**): let `Φ : H → ℂ` be
  measurable, left `Λ`-invariant and integrable on `sH`. Suppose `0 < ν(sN) < ∞`, and that for
  some `v₀ ∈ N` and `c ≠ 1`,
  `Φ(n v₀ x) = c Φ(n x)` for all `n ∈ N` and `x ∈ H`. Then `∫_{sH} Φ dμ = 0`.

## Proof

The Library's `RankinSelbergGlobal.Unfolding.integrable_and_integral_average` shows that
`(n, x) ↦ Φ(n x)` is integrable on `sN × sH` for `ν × μ` and that its integral is
`ν(sN) · ∫_{sH} Φ dμ`. By Fubini this is the integral over `x ∈ sH` of the inner averages
`∫_{sN} Φ(n x) dν(n)`. For each `x`, the function `n ↦ Φ(n x)` is left `Λ`-invariant. By
`setIntegral_mul_right_eq` and the hypothesis on `v₀`, its average `A` satisfies `c A = A`. So
`A = 0`, and the outer integral vanishes. Since `ν(sN) ≠ 0`, so does `∫_{sH} Φ dμ`.

In the application (`setIntegral_cellIntegrand_eq_zero` in
[CuspidalPairEisensteinUnfoldingCellIntegral.md](CuspidalPairEisensteinUnfoldingCellIntegral.md)),
`H = N₀(𝔸)`, `N` is the pattern group `Λ_J(𝔸)`, `Λ = Λ_J(F)`, and `v₀` is a root element
`1 + y₀ E_(k,k+1)` with `k ∉ J`, `k + 1 ∈ J` and `ψ(y₀) ≠ 1`, and `c = conj(ψ(y₀))`. This
implements the vanishing in Shahidi, *Functional equation satisfied by certain L-functions*,
Compositio Math. 37 (1978), proof of Lemma 2.1, paragraph after (2.10.3), p. 182. There the
integral over `V_𝔸 / V_F`, `V = wPw⁻¹ ∩ U`, factors through the character integral over
`(V_w)_𝔸 / (V_w)_F`, `V_w = U ∩ wNw⁻¹`, which vanishes when `V_w` is nontrivial. In the
application the root group of `v₀` lies in the analogue of `V_w`, and right translation by `v₀`
multiplies the averaged function by `c ≠ 1`
([CuspidalPairEisensteinUnfoldingCells.md](CuspidalPairEisensteinUnfoldingCells.md)).
