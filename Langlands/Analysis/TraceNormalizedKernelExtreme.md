# Extreme points of the trace-normalized kernel set

Module `Langlands.Analysis.TraceNormalizedKernelExtreme` continues
`Langlands.Analysis.TraceNormalizedKernelCone`. Its main result,
`eq_zero_or_one_of_extreme`, says: for strictly positive weights `c` (`hc : ∀ k, 0 < c k`) and a nonzero
extreme point `F` of `coneSet Rel c e`, every orthogonal projection on the Hilbert space of `F` that commutes with the
representation `rho` of `𝒜` is `0` or `1`. This is the analogue of Folland's Theorem 3.25 (an
extreme point of the normalized functions of positive type gives an irreducible representation;
G. B. Folland, *A Course in Abstract Harmonic Analysis*, 2nd ed., 2015, §3.3, printed p.86) for
the trace-normalized kernels.

## The Hilbert space of a cone element

For `hF : IsConeElement Rel F`:

| Declaration | Content |
| --- | --- |
| `kernel hF`, `Space hF`, `vec hF x k w` | the positive kernel `kernelOf F`, its Hilbert space (`Langlands.Analysis.PositiveKernel.Space`) and vectors, with `⟪vec x k w, vec y k' w'⟫ = F (k, k', x^* y, w, w')` (`inner_vec`) |
| `ext_vec`, `clm_ext` | extensionality on the spanning vectors |
| `vec_add`, `vec_smul`, `vec_add_w`, `vec_smul_w` | `vec` is linear in `x` and in `w` |
| `rho hF a` | left multiplication `vec x k w ↦ vec (a x) k w`, bounded by `‖a‖` by the domination condition (`norm_rho_le`) |
| `adjoint_rho`, `inner_rho`, `rho_mul`, `rho_one` | `rho` is a unital `*`-representation |
| `norm_vec_sq`, `re_diag_nonneg` | `‖vec x k w‖² = Re F (k, k, x^* x, w, w)` |
| `vec_rel` | a relation `(k₁, b, k₂, A)` gives `vec (b^*) k₁ w = vec 1 k₂ (A w)` |
| `vecL hF hB x k` | for bounded `F`, the bounded operator `w ↦ vec x k w` |

## Compressions

For a bounded linear `Q` on `Space hF`, `compress hF Q (k, k', x, w, w') = ⟪Q (vec 1 k w), vec x k' w'⟫`.
`compress_one` gives `F`, `compress_add` and `compress_one_sub` give additivity. If `Q` is a star
projection commuting with every `rho a`, then `kernelOf (compress Q)` is the Gram kernel
`⟪Q (vec i), vec j⟫` (`kernelOf_compress`) and `compress Q` is again a cone element for the same
relations (`isConeElement_compress`); it is a bounded form when `F` is (`isBoundedForm_compress`).

## Weighted traces

`traceW c e F = ∑_{k,b} ofReal (c_k Re F (k, k, 1, e_b, e_b))` and
`traceK e F k = ∑_b ofReal (Re F (k, k, 1, e_b, e_b))` in `ℝ≥0∞`, where `ofReal = ENNReal.ofReal`
clips each summand to `[0, ∞)` separately. For bounded cone elements:

* `opNorm_le_sqrt_tsum`: the operator norm is at most the Hilbert–Schmidt norm on a Hilbert basis;
  applied to `vecL hF hB 1 k` it gives `norm_vecL_le`;
* `norm_le_traceK`: if `traceK e F k < ∞` and `traceK e F k' < ∞`, then
  `|F (k, k', x, w, w')| ≤ ‖x‖ ‖w‖ ‖w'‖ √((traceK e F k).toReal · (traceK e F k').toReal)`;
* `norm_le_traceW`: if every `c_k` is positive and `traceW c e F < ∞`, then
  `|F (k, k', x, w, w')| ≤ ‖x‖ ‖w‖ ‖w'‖ · (traceW c e F).toReal / √(c_k c_{k'})`
  (via `ofReal_mul_traceK_le`, `traceK_lt_top`, `toReal_traceK_le`: `c_k traceK ≤ traceW`);
* `traceW_zero_imp`: if every `c_k` is positive, `traceW c e F = 0` forces `F = 0`;
* `traceW_smul`: positive homogeneity; `traceW_add`: additivity on cone elements when every `c_k`
  is positive;
* `traceW_le_one_iff`, `mem_coneSet_of`, `smul_inv_mem_coneSet`, `zero_mem_coneSet`,
  `isBoundedForm_of_mem`: membership in `coneSet`, in particular `traceW⁻¹ • F ∈ coneSet` when
  `0 < traceW F < ∞`.

## Extreme points

The results of this section and the membership results above, except `zero_mem_coneSet` and
`isBoundedForm_of_mem`, assume strictly positive weights (`hc : ∀ k, 0 < c k`). `traceW_eq_one_of_extreme`: a nonzero extreme point has weighted trace `1` (otherwise it lies on
the open segment from `0` to its normalization). `compress_eq_smul_of_extreme`: for a projection
`Q` as above, `F = compress Q + compress (1 - Q)` with both summands bounded cone elements; with
`t = traceW (compress Q)`, either a summand vanishes or `F` lies on the open segment between the
normalized summands, and extremality gives `compress Q = t • F`. Then `⟪Q vec i, vec j⟫ = t ⟪vec i, vec j⟫`
for all indices, so `Q = t • 1`, and `Q² = Q` gives `Q = 0` or `Q = 1`
(`eq_zero_or_one_of_extreme`).

## Provenance

Internal; the argument follows the pattern of Folland's proof of Theorem 3.25 (§3.3, printed
pp.86–87), with the trace normalization of `Langlands.Analysis.TraceNormalizedKernelCone`.
