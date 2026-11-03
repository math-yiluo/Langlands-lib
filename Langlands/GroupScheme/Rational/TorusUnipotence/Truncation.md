# Algebra maps into truncations that are the identity to first order

Module `Langlands.GroupScheme.Rational.TorusUnipotence.Truncation`, namespace
`Langlands.GroupScheme.TorusUnipotence`.

This module proves a kernel criterion used in `TruncatedSection` and `BigCell`. Let `𝔪` be an
ideal of a `k`-algebra `B` with `B = k + 𝔪`. If an algebra map `e : B → B ⧸ 𝔪 ^ N` agrees with
the quotient map to first order on generators of `𝔪`, then the kernel of `e` lies in `𝔪 ^ N`.

## Statements

Let `k`, `B`, `R` be commutative rings with `B` and `R` `k`-algebras.

* `sub_mem_of_map_le 𝔪 hB J e f he hf p`. Suppose every `b ∈ B` is congruent to a constant
  `algebraMap k B c` modulo `𝔪` (`hB`), and that the algebra maps `e f : B →ₐ[k] R` both send `𝔪`
  into the ideal `J` of `R`. Then `e p - f p ∈ J` for every `p`.
* `sub_mem_sq_of_mem 𝔪 S hS hB J e f he hf hgen hp`. In the same situation, let `S` generate
  `𝔪` (`Ideal.span S = 𝔪`) and suppose `e s - f s ∈ J ^ 2` for `s ∈ S`. Then
  `e p - f p ∈ J ^ 2` for every `p ∈ 𝔪`.
* `sub_mem_pow_succ`: under the same hypotheses, `e p - f p ∈ J ^ (m + 1)` for every `m` and
  every `p ∈ 𝔪 ^ m`.
* `mem_pow_of_eq_zero_of_span 𝔪 S hS hB e he hp`. Let `S` generate `𝔪`, let `B = k + 𝔪`, and let
  `e : B →ₐ[k] B ⧸ 𝔪 ^ N` satisfy `e s - [s] ∈ (𝔪 · (B ⧸ 𝔪 ^ N)) ^ 2` for `s ∈ S`, where `[s]` is
  the class of `s`. If `e p = 0`, then `p ∈ 𝔪 ^ N`.

For polynomial rings `MvPolynomial σ k` with the ideal `idealOfVars σ k` of the variables:

* `sub_C_constantCoeff_mem_idealOfVars p`: `p - C (constantCoeff p)` lies in the ideal of the
  variables.
* `mem_idealOfVars_iff p`: `p` lies in the ideal of the variables iff its constant coefficient is
  `0`.
* `mem_pow_of_eq_zero e he hp`: the case `B = MvPolynomial σ k`, `𝔪 = idealOfVars σ k`,
  `S = {X s}` of `mem_pow_of_eq_zero_of_span`.

## Proof

*First order.* Write `p = c + (p - c)` with `p - c ∈ 𝔪`. Both `e` and `f` fix the constant `c`,
and `e (p - c)` and `f (p - c)` lie in `J`.

*Second order.* Induct over `Ideal.span S` (`Submodule.span_induction`). Generators hold by
hypothesis, and zero and sums are immediate. For a product `r * x` with `x ∈ 𝔪`, write
`e r e x - f r f x = e r (e x - f x) + (e r - f r) f x`. The first term lies in `J ^ 2` by
induction, and the second in `J · J` by the first-order step and `f x ∈ J`.

*Higher order.* Induct on `m`, using `Submodule.mul_induction_on` for `𝔪 ^ (m + 2) = 𝔪 ^ (m + 1) · 𝔪`.
For a product `a b` with `a ∈ 𝔪 ^ (m + 1)` and `b ∈ 𝔪`, the same splitting gives
`e a (e b - f b) ∈ J ^ (m + 1) · J ^ 2` and `(e a - f a) f b ∈ J ^ (m + 2) · J`, using
`Ideal.map_pow` for `e a ∈ J ^ (m + 1)`.

*Kernel criterion.* Take `R = B ⧸ 𝔪 ^ N`, `J = 𝔪 · R` and `f` the quotient map. Generators of
`𝔪` are sent into `J` by `f`, and by `e` because `e s = (e s - [s]) + [s]` with `J ^ 2 ⊆ J`. So
both maps send `𝔪` into `J`. Then show `p ∈ 𝔪 ^ m` for all `m ≤ N` by induction on `m`. If
`p ∈ 𝔪 ^ m`, then `0 - [p] = e p - f p ∈ J ^ (m + 1) = (𝔪 ^ (m + 1)) · R`. By
`Ideal.mem_quotient_iff_mem_sup`, `p ∈ 𝔪 ^ (m + 1) ⊔ 𝔪 ^ N = 𝔪 ^ (m + 1)`.

*Polynomials.* `mem_pow_idealOfVars_iff'` characterizes `idealOfVars ^ n` by the vanishing of
the coefficients of degree `< n`. With `n = 1` this is the constant coefficient.

## Provenance

These are standard commutative-algebra facts, proved here as internal lemmas for the proof of
`Langlands.GroupScheme.RelativeRoot.TorusActionUnipotenceStatement`. No source states them in
this form.
