# Differentiating Whittaker functions along archimedean square-zero directions

Module `Langlands.Global.RankinSelberg.WhittakerExpansionCore.WhittakerDeriv`, namespace
`Langlands.Global.RankinSelbergGlobal.Unfolding`. These are helper lemmas for half (S) of the
Whittaker expansion (see `Interface`). The Whittaker integral may be differentiated under the
integral sign along a one-parameter subgroup `t ↦ 1 + tZ` of the archimedean component.

## Section `ArchPoint`

Let `Z` be an archimedean matrix with `Z * Z = 0`.

* `squareZeroElement_add_smul`: `(1 + sZ)(1 + tZ) = 1 + (s + t)Z` in `GL_n(F_∞)`. Proof: expand
  the product. The term `s t Z²` vanishes.
* `archPoint_add_smul`: the same identity for the adelic points `archPoint F n (t • Z)`, by
  applying the inverse of `adelicEquiv ∘ ofInfinite`, which is multiplicative.
* `archPoint_zero_smul`: `archPoint F n (0 • Z) = 1`.
* `continuous_archPoint_smul`: `t ↦ archPoint F n (t • Z)` is continuous. Proof: composition of the
  Library's `ArchimedeanGL.continuous_squareZeroElement_smul`, the continuous embedding
  `AdelicGL.ofInfinite`, and the inverse of the homeomorphism
  `GeneralLinearGroupPoints.adelicHomeomorph`.

## Section `Derivative`

* `hasDerivAt_whittaker`: let `ψ` be a standard additive character. Let `f`, `f'` be continuous
  functions on `GL_{r+1}(𝔸)`, left invariant under `GL_{r+1}(F)` and bounded on every band
  `lo ≤ |det x|_𝔸 ≤ hi` with `0 < lo`. Suppose that for every `x` the function
  `t ↦ f(x (1 + tZ))` has derivative `f'(x)` at `t = 0`. Then for every `g` the function
  `t ↦ W_f(g (1 + tZ))` has derivative `W_{f'}(g)` at `t = 0`.

  Proof. Write `a(t) = archPoint(tZ)` and `d = |det g|_𝔸 > 0`. The set `s` of `t` with
  `d/2 < |det(g a(t))|_𝔸 < 2d` is a neighbourhood of `0`, because `t ↦ |det(g a(t))|_𝔸` is
  continuous and equals `d` at `0`. For `t ∈ s` and `u ∈ N(𝔸)`, the point `u g a(t)` lies in the
  band `[d/2, 2d]`. There `f` and `f'` are bounded by constants `B` and `B'`. Write both
  Whittaker functions as set integrals over the fundamental domain of `N(F)` in `N(𝔸)`
  (`whittaker_eq_setIntegral`). This domain has finite measure. Mathlib's
  `hasDerivAt_integral_of_dominated_loc_of_deriv_le` applies with the constant bound `B'`. The
  pointwise derivative at `t` comes from the hypothesis at the point `n g a(t)`, via
  `a(t + τ) = a(t) a(τ)` (`archPoint_add_smul`).
