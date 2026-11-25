# Extracting one coefficient of an absolutely convergent exponential series

Module `Langlands.Global.EisensteinGenericInjectivity.Cesaro` shows that an absolutely
convergent series `∑_c B(c) e^{i y θ(c)}` with a coefficient `B(c₀) ≠ 0` at a frequency
`θ(c₀)` taken by no other index does not vanish at every point of a suitable arithmetic
progression of `y` (`exists_shift_tsum_ne_zero`). The module
`Langlands.Global.EisensteinGenericInjectivity.Anchor` applies it to the determinant of
Eisenstein series along an imaginary line.

All declarations are in the namespace `Langlands.Global.EisensteinGenericInjectivity`. Complete
types are printed by `PrettyPrinter.ppSignature` (the `#check` form), with the namespaces of the
page of `Langlands.Global.EisensteinGenericInjectivity.PlaceHeight` open.

## Declarations

- `tendsto_cesaro_pow_zero`: for `z ∈ ℂ` with `‖z‖ = 1` and `z ≠ 1`, the Cesàro means
  `M⁻¹ ∑_{m<M} z^m` tend to `0`.
  ```lean
  Langlands.Global.EisensteinGenericInjectivity.tendsto_cesaro_pow_zero {z : ℂ} (hz : ‖z‖ = 1)
    (h1 : z ≠ 1) :
    Filter.Tendsto (fun M => (↑M)⁻¹ * ∑ m ∈ Finset.range M, z ^ m) Filter.atTop (nhds 0)
  ```
- `norm_cesaro_pow_le`: these means have norm at most `1` when `‖z‖ = 1`.
  ```lean
  Langlands.Global.EisensteinGenericInjectivity.norm_cesaro_pow_le {z : ℂ} (hz : ‖z‖ = 1) (M : ℕ) :
    ‖(↑M)⁻¹ * ∑ m ∈ Finset.range M, z ^ m‖ ≤ 1
  ```
- `coeff_eq_zero_of_forall_pow_tsum_eq_zero`: let `B` be absolutely summable and `ζ` take values
  of norm one, with `ζ c₀ = 1` and `ζ c ≠ 1` for `c ≠ c₀`. If every moment
  `∑'_c B(c) ζ(c)^m`, `m ∈ ℕ`, vanishes, then `B(c₀) = 0`.
  ```lean
  Langlands.Global.EisensteinGenericInjectivity.coeff_eq_zero_of_forall_pow_tsum_eq_zero.{u_1}
    {«ι» : Type u_1} {B ζ : «ι» → ℂ} {c₀ : «ι»} (hB : Summable fun c => ‖B c‖)
    (hζ : ∀ (c : «ι»), ‖ζ c‖ = 1) (hζ₀ : ζ c₀ = 1) (hζ₁ : ∀ (c : «ι»), c ≠ c₀ → ζ c ≠ 1)
    (h : ∀ (m : ℕ), ∑' (c : «ι»), B c * ζ c ^ m = 0) : B c₀ = 0
  ```
- `exists_scale_ne_one`: let `θ` be real frequencies on a countable index type such that `c₀`
  is the only index of frequency `θ(c₀)`. Then some real `τ` makes every
  `exp(i τ (θ(c) − θ(c₀)))`, `c ≠ c₀`, different from `1`.
  ```lean
  Langlands.Global.EisensteinGenericInjectivity.exists_scale_ne_one.{u_1} {«ι» : Type u_1}
    [Countable «ι»] (θ : «ι» → ℝ) (c₀ : «ι») (hθ : ∀ (c : «ι»), c ≠ c₀ → θ c ≠ θ c₀) :
    ∃ τ, ∀ (c : «ι»), c ≠ c₀ → Complex.exp (Complex.I * ↑(τ * (θ c - θ c₀))) ≠ 1
  ```
- `exists_shift_tsum_ne_zero` (**coefficient extraction**): under the hypotheses of
  `exists_scale_ne_one`, if `B` is absolutely summable and `B(c₀) ≠ 0`, there are `τ ∈ ℝ` and
  `m ∈ ℕ` with `∑'_c B(c) exp(i m τ θ(c)) ≠ 0`.
  ```lean
  Langlands.Global.EisensteinGenericInjectivity.exists_shift_tsum_ne_zero.{u_1} {«ι» : Type u_1}
    [Countable «ι»] {B : «ι» → ℂ} {θ : «ι» → ℝ} {c₀ : «ι»} (hB : Summable fun c => ‖B c‖)
    (hθ : ∀ (c : «ι»), c ≠ c₀ → θ c ≠ θ c₀) (h₀ : B c₀ ≠ 0) :
    ∃ τ m, ∑' (c : «ι»), B c * Complex.exp (Complex.I * ↑(↑m * τ * θ c)) ≠ 0
  ```

## Proofs

- `tendsto_cesaro_pow_zero`: the geometric sum `∑_{m<M} z^m = (z^M − 1)/(z − 1)` has norm at
  most `2/‖z − 1‖`.
- `coeff_eq_zero_of_forall_pow_tsum_eq_zero`: average the vanishing moments over `m < M`. The
  averaged weight is `1` at `c₀` and tends to `0` elsewhere, and it is bounded by `1`, so
  dominated convergence for series (`tendsto_tsum_of_dominated_convergence`) gives
  `0 = lim_M ∑'_c B(c) M⁻¹ ∑_{m<M} ζ(c)^m = B(c₀)`.
- `exists_scale_ne_one`: a bad `τ` lies in one of the countably many countable sets
  `2πℤ / (θ(c) − θ(c₀))`, and the complement of a countable subset of `ℝ` is dense, hence
  nonempty.
- `exists_shift_tsum_ne_zero`: with `ζ(c) = exp(i τ (θ(c) − θ(c₀)))`, the series at `y = m τ`
  is `exp(i m τ θ(c₀)) ∑'_c B(c) ζ(c)^m`; if all of them vanished,
  `coeff_eq_zero_of_forall_pow_tsum_eq_zero` would give `B(c₀) = 0`.

## Sources

Elementary analysis; no literature source.
