# The open-cell integral for the `(1, n)` parabolic

Module `Langlands.Representation.Shahidi.OpenCellBaseInduction`, namespace
`Langlands.Shahidi.OpenCell.Base`.

## Main result

`integral_baseIntegrand`: for `ψ` of conductor `𝒪`, every function `Ψ` of Whittaker type on
`GL_(t+1)(K)` and every `d ∈ ℤ`,

`∫ F_(d,Ψ)(lower Y) conj ψ(Y_last) dY = baseValue ϖ t d Ψ`,

where `F_(d,Ψ)` is the lift of `shellΦ d Ψ` and the integral is for `matrixHaar`. The value
`baseValue ϖ t d Ψ` is `0` for `d < 0` and for `d > t + 1`; for `0 ≤ d ≤ t + 1`, with
`D = d.toNat`, it is

`(-1)^D q^(α(t+1, D)) Ψ(ϖ^(κ(t,D)))`,

where `baseAlpha n D = α(n, D) = ∑_(j<D) (n-1-j)` and `baseKappa t D = κ(t, D) =
(0, …, 0, -1, …, -1)` has `min(D, t+1)` last entries equal to `-1` (in this range, `D` of
them).

## Proof

Induction on `t`. For `t = 0` (`integral_baseIntegrand_zero`) the `GL_2` open cell is computed
directly (`lower_eq_GL2`). For the step (`integral_baseIntegrand_succ`) the last entry `c` of the
column is separated by Fubini (`Langlands.Representation.Shahidi.OpenCellColumn`): for `c`
integral the inner integral is `[d = 0] Ψ(1)` (`inner_of_mem`, which uses the conductor); for a second block of rank `n` and `|c| = q^e` with `e ≥ 1`,
the inner integral over the remaining `n - 1` entries (`inner_of_valuation`) is
`conj ψ(c) · q^(e(n-1))` times the smaller-rank integral of the degree-`(d - e)` piece for
`twistOne Ψ e`: the change of variables `y ↦ c⁻¹ y` contributes the Haar factor
`|c|^(n-1) = q^(e(n-1))`, and `z ↦ -z` restores the character (`integral_char_mul_liftFunction`).
The integrals of `conj ψ` over the shells give `-1` for `e = 1` and `0` for `e ≥ 2`
(`integral_outer`), so only `e = 1` contributes, and its factor `q^(n-1)` is the increment
`n - 1` of `α` (`baseAlpha_succ`).

## Provenance

Derived; this is the rank-one case of the open-cell (Jacquet) integral, computed directly for
an arbitrary Whittaker-type function on the second block.
