# Recurrent multipliers on a parity class of integers

Module `Langlands.Representation.Archimedean.RealBlockMultiplier`, namespace
`Langlands.Archimedean.RealBlockMultiplier`.

## Role and provenance

This is internal, elementary algebra: sequences `μ : ℤ → ℂ` and explicit binomial and
product formulas. It makes no claim from the literature and has no sources. It serves the
proof of `Langlands.Archimedean.RealCharacterPairFiltrationStatement` (Task 7067). There, a
linear map between principal series of `GL_2(ℝ)` in the block coordinates `p, p + 1`
multiplies the `k`-th rotation Fourier coefficient of a function by a scalar `μ k`. Its
compatibility with the Lie algebra action becomes the recurrence below, and its
compatibility with the sign reflections the symmetry below. Those equivalences are proved in
the modules that use the multipliers. This module only solves the recurrence, with explicit
finite products and binomial coefficients checked directly against it. The three
constructions are the ones the proof is planned to use:

* a solution without zeros, for an isomorphism in the irreducible case;
* a binomial solution supported on `|k| < ℓ`, for the map onto the finite-dimensional
  modes in the reducible case;
* a tail solution supported on `|k| > ℓ`, for the map onto the discrete-series block.

## Definitions

Throughout, `ε : ℤ` is the parity (`ε = 0 ∨ ε = 1` in all results) and `k` ranges over the
parity class `k ≡ ε (mod 2)`, written `Even (k - ε)`.

* `IsRecurrent δ ε μ`: for every `k` in the parity class,
  `μ (k + 2) · (δ + k) = (k + 2 - δ) · μ k`.
* `IsSymmetric ε σ μ`: for every `k` in the parity class, `μ (-k) = σ · μ k`.
* `extend σ a` for `a : ℕ → ℂ` is the function `k ↦ a (|k| / 2)` for `k ≥ 0` and
  `k ↦ σ · a (|k| / 2)` for `k < 0` (natural-number division). On the parity class of
  `ε ∈ {0, 1}`, its value at `ε + 2m` is `a m` and at `-(ε + 2m)` it is `σ · a m`, except at
  `k = 0`, where it is `a 0`.
* `genericSeq ν ε m = ∏_{i<m} (ε + 2i + 1 - ν) / (ε + 2i + 1 + ν)` and
  `genericMultiplier ν ε = extend ((-1)^|ε|) (genericSeq ν ε)`.
* `binomialSeq ℓ ε m = (-1)^m · C(ℓ - 1, (ℓ - 1 + ε) / 2 + m)` (natural-number arithmetic, with
  `ε` read as a natural number through `Int.toNat`) and
  `binomialMultiplier ℓ ε = extend ((-1)^|ε|) (binomialSeq ℓ ε)`. When `ℓ - 1 ≡ ε`, the lower
  index is `(k + ℓ - 1) / 2` for `k = ε + 2m`.
* `tailSeq ℓ ε m = C(m + (ℓ - 1 + ε) / 2, ℓ)` and
  `tailMultiplier ℓ ε σ = extend σ (tailSeq ℓ ε)`. When `ℓ - 1 ≡ ε`, the upper index is
  `(k + ℓ - 1) / 2` for `k = ε + 2m`.

## Results

Inverses:

* `IsRecurrent.inv`: if `IsRecurrent δ ε μ` and `μ` has no zeros on the parity class, then
  `IsRecurrent (2 - δ) ε (fun k => (μ k)⁻¹)`. For `δ = ν + 1` this gives `1 - ν`.
* `IsSymmetric.inv`: `IsSymmetric ε σ μ` implies `IsSymmetric ε σ⁻¹ (fun k => (μ k)⁻¹)`.

Extension by symmetry. Let `ε = 0 ∨ ε = 1` and `σ² = 1`, and suppose that `a 0 = 0` or
`σ = (-1)^|ε|` (the compatibility at the centre of the class).

* `isSymmetric_extend`: `extend σ a` is symmetric for `σ`.
* `isRecurrent_extend`: if `a (m + 1) · (δ + ε + 2m) = (ε + 2m + 2 - δ) · a m` for all
  `m : ℕ`, then `IsRecurrent δ ε (extend σ a)`.
* `extend_ne_zero_iff`: for `σ ≠ 0`, `extend σ a k ≠ 0 ↔ a (|k| / 2) ≠ 0`.

The generic multiplier. Let `0 < re ν`, `ε = 0 ∨ ε = 1` and `ν ≠ ε + 2m + 1` for all `m : ℕ`.

* `isRecurrent_genericMultiplier`: `IsRecurrent (ν + 1) ε (genericMultiplier ν ε)`. This needs
  only `0 < re ν`, which makes the denominators `ε + 2i + 1 + ν` nonzero.
* `isSymmetric_genericMultiplier`: symmetric for `(-1)^|ε|`.
* `genericMultiplier_ne_zero`: no zeros at all.
* `exists_generic`: there is `μ` with `IsRecurrent (ν + 1) ε μ`,
  `IsSymmetric ε ((-1)^|ε|) μ` and `μ k ≠ 0` on the parity class.

The binomial and tail multipliers. Let `ℓ : ℕ` with `0 < ℓ`, `ε = 0 ∨ ε = 1` and
`Even ((ℓ : ℤ) - 1 - ε)`. Then `exists_half` gives `h : ℕ` with `ℓ = ε + 2h + 1`.

* `isRecurrent_binomialMultiplier`: `IsRecurrent (ℓ + 1) ε (binomialMultiplier ℓ ε)`.
* `isSymmetric_binomialMultiplier`: symmetric for `(-1)^|ε|`.
* `binomialMultiplier_ne_zero_iff`: on the parity class, `binomialMultiplier ℓ ε k ≠ 0 ↔ |k| < ℓ`.
* `exists_binomial`: there is `μ` with `IsRecurrent (ℓ + 1) ε μ`,
  `IsSymmetric ε ((-1)^|ε|) μ` and, on the parity class, `μ k ≠ 0 ↔ |k| < ℓ`.
* For any `σ` with `σ² = 1`: `isRecurrent_tailMultiplier`, that is
  `IsRecurrent (1 - ℓ) ε (tailMultiplier ℓ ε σ)`; `isSymmetric_tailMultiplier` (symmetric
  for `σ`); `tailMultiplier_ne_zero_iff`, that is `tailMultiplier ℓ ε σ k ≠ 0 ↔ ℓ < |k|` on
  the parity class.
* `exists_tail`: there is `P` with `IsRecurrent (1 - ℓ) ε P`, `IsSymmetric ε σ P` and, on the
  parity class, `P k ≠ 0 ↔ ℓ < |k|`.

## Proofs

* `IsRecurrent.inv` multiplies the recurrence at `k` by `(μ k)⁻¹ (μ (k + 2))⁻¹`, which is
  possible because `k + 2` lies in the same parity class (`linear_combination` with
  `(μ k)⁻¹ μ k = 1` and `(μ (k + 2))⁻¹ μ (k + 2) = 1`).
* `isSymmetric_extend`: for `k ≠ 0` it uses `|−k| = |k|` and `σ² = 1`. At `k = 0`, which lies
  in the class only for `ε = 0`, it uses the centre hypothesis.
* `recurrence_of_reflect`: for a symmetric `μ` with `σ² = 1`, the recurrence at `k` follows
  from the recurrence at `-k - 2`. The substitution `k ↦ -k - 2` maps `μ (k + 2)` to
  `σ μ k` and `μ k` to `σ μ (k + 2)`, and the identity is the original one multiplied by `-σ`.
* `isRecurrent_extend` splits into three cases. For `k ≥ 0`, write `k = ε + 2m`; then
  `|k + 2| / 2 = m + 1` and the identity is the hypothesis on `a` at `m`. For `k = -1` (only
  for `ε = 1`), it is `a 0 · (δ - 1) = (1 - δ) σ a 0`, which holds if `a 0 = 0` or `σ = -1`.
  For `k ≤ -2`, apply `recurrence_of_reflect` with `-k - 2 ≥ 0`.
* Generic: `genericSeq (m + 1) = genericSeq m · (ε + 2m + 1 - ν) / (ε + 2m + 1 + ν)` by
  `Finset.prod_range_succ`. The denominator has real part `ε + 2m + 1 + re ν > 0`, so the
  identity follows by `field_simp`. Every factor is nonzero because `ν ≠ ε + 2i + 1`.
* Binomial: with `ℓ = e + 2h + 1` (`e = ε`), `binomialSeq ℓ ε m = (-1)^m C(e + 2h, e + h + m)`
  (`binomialSeq_eq`). The recurrence for `δ = ℓ + 1` becomes
  `C(n, c + 1)(c + 1) = C(n, c)(n - c)` with `n = e + 2h` and `c = e + h + m`, which is
  `Nat.choose_succ_right_eq`. If `c > n`, both binomial coefficients vanish. The coefficient
  is nonzero iff `e + h + m ≤ e + 2h`, that is `m ≤ h`, that is `|k| = e + 2m < ℓ`.
* Tail: `tailSeq ℓ ε m = C(m + e + h, ℓ)` (`tailSeq_eq`). With `N = m + e + h`, the recurrence
  for `δ = 1 - ℓ` becomes `C(N, ℓ)(N + 1) = C(N + 1, ℓ)(N + 1 - ℓ)`, which is
  `Nat.choose_mul_succ_eq`. If `ℓ > N + 1`, both sides vanish. The coefficient is nonzero iff
  `ℓ ≤ m + e + h`, that is `h < m`, that is `|k| = e + 2m > ℓ`. In particular
  `tailSeq ℓ ε 0 = 0`, so the centre condition of the extension holds for every `σ`.
