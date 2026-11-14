# Valuation lattices for the ramified quadratic unitary integral models

Module `Langlands.GroupScheme.Examples.SU3RootUnitaryLattices`, namespace
`Langlands.GroupScheme.SU3Root`.

This module proves the valuation arithmetic of Kaletha–Prasad (KP) §2.8, §3.2 and Appendix C.4
that the integral models `X_{r,s}` of the unitary parameter group need. KP state these
results for a separable quadratic extension of a field with a discrete valuation. Here the
setting is a separable quadratic field extension `L / K` (`Algebra.IsQuadraticExtension`,
`Algebra.IsSeparable`) with nontrivial automorphism `σ = conjugation K L`, together with an
additive valuation `ω : AddValuation L (WithTop ℝ)` satisfying explicit hypotheses. Mathlib's
`AddValuation` uses the `min` convention, `ω(x + y) ≥ min(ω x, ω y)`, with `ω 0 = ⊤`. No
completeness, Henselian property or residue field is used.

## Hypotheses

`IsRamifiedQuadraticValuation K L ω` (a `Prop`-valued structure) asks for three things:

- `conjugation_eq`: `ω (σ z) = ω z` for all `z ∈ L`;
- `base_int`: for every nonzero `a ∈ K`, `ω a` is an integer;
- `exists_half`: some `π ∈ L` has `ω π = 1/2`.

These are the properties KP use in C.4 when `L / K` is ramified and `ω` is the extension to `L`
of the valuation on `K` normalized so that `ω(K^×) = ℤ` (KP, C.4, the convention
`ω(K^×) = ℤ`, and the ramification of `L / K` noted there). The structure records only the
inclusion `ω(K^×) ⊆ ℤ`. Equality follows: `baseUniformizer` has value `1`.

## Basic consequences (namespace `IsRamifiedQuadraticValuation`, hypothesis `hω`)

- `uniformizer` is a chosen `π` with `ω π = 1/2`. It is not in `K`, because values on `K` are
  never half-odd integers (`omega_algebraMap_ne_half`). Hence `uniformizerBasis` is the
  `K`-basis `(1, π)` of `L`, and `exists_decomposition` writes every element as `c₀ + c₁ π`.
- `omega_add_mul_uniformizer`: `ω(c₀ + c₁ π) = min(ω c₀, ω c₁ + 1/2)`. The two values are
  distinct, the first in `ℤ ∪ {⊤}` and the second in `ℤ + 1/2 ∪ {⊤}`, unless both are `⊤`.
- `baseUniformizer` is a chosen `ϖ ∈ K` with `ω ϖ = 1`. It exists because `π σ(π)` is
  `σ`-invariant, so it lies in `K`, and its value is `1`. `omega_baseUniformizer_zpow` gives
  `ω(ϖ^n) = n` for `n ∈ ℤ`.
- `exists_half_integer`: every nonzero `x` has `ω x ∈ (1/2) ℤ`, since `2 ω(x) = ω(x σ(x))`
  and `x σ(x) ∈ K`.

General helpers outside the namespace: `exists_omega_eq_coe` (nonzero elements have real
values), `omega_zpow` (values of integer powers), `coe_le_add_coe_iff`,
`le_int_add_ceil_iff` (`t ≤ n + ⌈t⌉ ↔ 0 ≤ n` for `n ∈ ℤ`), and `int_ne_int_add_half`.

## The number `μ` (KP (2.8.1), (2.8.2))

- `mu K L ω = sSup {t ∈ ℝ | ∃ x, x + σ x = 1 ∧ ω x = t}` is KP's
  `μ = sup {ω(x) | x ∈ L_{tr=1}}` (2.8.1).
- `omega_le_zero_of_add_eq_one`: trace-one elements have `ω x ≤ 0`, as KP note.
- `isGreatest_mu`: the supremum is a maximum. The values lie in `(1/2) ℤ` and are bounded
  above by `0`, and the published `traceOne K L` shows the set is nonempty. Consequences:
  `omega_le_mu` (every trace-one `x` has `ω x ≤ μ`), `mu_le_zero`, and
  `exists_traceOne_omega_eq_mu`.
- `traceOneMax` is a chosen `λ ∈ L_{tr=1,max}` (KP (2.8.2)), with `λ + σ λ = 1`
  (`traceOneMax_add`) and `ω λ = μ` (`omega_traceOneMax`).

KP's formula `μ = −s/2`, involving the ramification jump `s`, is not formalized here.

## Lemma 2.8.1(2): values of trace-zero elements

- `traceZero_parity`: if `y ≠ 0` and `y + σ y = 0`, then `ω y = m + 1/2 + μ` for some
  `m ∈ ℤ`.
- `exists_traceZero_omega_eq`: conversely, every `m + 1/2 + μ` with `m ∈ ℤ` is the value of a
  trace-zero element. Take `ϖ^(m − m₀) f₀`, where `f₀ = traceZeroElement K L` is a chosen
  nonzero trace-zero element (`traceZeroElement_ne_zero`, `traceZeroElement_add`) of value
  `m₀ + 1/2 + μ`.

Together these give the second statement of KP Lemma 2.8.1(2): `ω(L^0 ∖ 0) = ℤ + 1/2 + μ`.

The Lean proof of `traceZero_parity` differs from KP's proof, which adjusts by a unit and
reduces modulo the maximal ideal. Write `y / λ = c₀ + c₁ π` with `c₀, c₁ ∈ K`.

- If `ω c₁ + 1/2 ≤ ω c₀`, then `c₁ ≠ 0` and `ω y = μ + ω c₁ + 1/2` with `ω c₁ ∈ ℤ`.
- Otherwise `c₀ ≠ 0`. The element `x' = λ − c₀⁻¹ y` has trace one, because `y` has trace
  zero. Also `x' = −c₀⁻¹ λ c₁ π`, so `ω x' = μ − ω c₀ + ω c₁ + 1/2 > μ`. This contradicts
  `omega_le_mu`.

`traceZero_add_half_le` is the form used later: for a trace-zero `z` and `n ∈ ℤ`,
`ω z ≥ n + μ` implies `ω z ≥ n + 1/2 + μ`.

## Lemma 3.2.2

KP Lemma 3.2.2 says the isomorphism `U_a(K)/U_{2a}(K) → L` identifies the filtrations, where
`U_a(K)_r = {(u, v) | ω(v) ≥ 2r + μ}` (KP (3.2.2)) and the filtration on `L` is
`{u | ω(u) ≥ r}`. The module proves the two inclusions in the form KP use in C.4:

- `le_omega_of_le_omega_second`: if `v + σ v = u σ(u)` and `ω v ≥ 2r + μ`, then `ω u ≥ r`.
  This is the direction cited in KP's proof of Lemma C.4.2.
- `le_omega_traceOneMax_mul`: if `ω u ≥ r`, then `ω(λ u σ(u)) ≥ 2r + μ`.

Proof of `le_omega_of_le_omega_second`. Assume `u ≠ 0`. Then `u σ(u) = c ∈ K` with
`ω c = n ∈ ℤ` and `ω u = n/2`. Suppose `n < 2r`. Then `w = λ c` has `ω w = μ + n < ω v`, so
`x = v − w` has value `μ + n`. But `x` has trace zero, because `λ + σ λ = 1`. By
`traceZero_parity`, `μ + n ∈ ℤ + 1/2 + μ`, which is impossible. This is KP's argument with
the parity statement made explicit.

## The lattices `Y_r` and `Z_s`

KP C.4 uses `Y_r = {u ∈ L | ω(u) ≥ r}` and `Z_s = {x ∈ L^0 | ω(x) ≥ s + μ}`.
"Integral" for `c ∈ K` means `ω c ≥ 0`.

- `le_omega_mul_zpow_ceil_iff`: `ω(d ϖ^⌈t⌉) ≥ t ↔ ω d ≥ 0`, for `d ∈ K` and real `t`.
- `latticeBasis r` is the `K`-basis `(ϖ^⌈r⌉, ϖ^⌈r − 1/2⌉ π)` of `L` (`latticeBasis_zero`,
  `latticeBasis_one`). It is `uniformizerBasis` rescaled by the units `latticeUnits r`.
  `latticeBasis_decomposition` expands an element in this basis.
- `le_omega_iff_latticeBasis`: for every real `r` and every `u ∈ L`, `ω u ≥ r` if and only
  if both coordinates of `u` in `latticeBasis r` are integral. So `Y_r` is the free
  `𝒪`-module on `latticeBasis r`. `le_omega_latticeBasis`: the basis vectors lie in `Y_r`.
- `traceZeroValue` is the value of `f₀` (`omega_traceZeroElement`).
  `latticeCenter s = ϖ^⌈s + μ − ω(f₀)⌉ f₀` is nonzero with trace zero
  (`latticeCenter_ne_zero`, `latticeCenter_add`).
- `le_omega_mul_latticeCenter_iff`: for `c ∈ K`,
  `ω(c · latticeCenter s) ≥ s + μ ↔ ω c ≥ 0`. `exists_mul_latticeCenter`: every trace-zero
  element is `c · latticeCenter s` for some `c ∈ K`. So `Z_s` is the free `𝒪`-module on
  `latticeCenter s`.

## Integrality of the correction (KP proof of Lemma C.4.2)

Recall `correction K L λ x y = σ(λ) x σ(y) − λ σ(x) y` from
`Langlands.GroupScheme.Examples.SU3RootUnitaryCoordinates`. It has trace zero and is the
bilinear term of the transported group law (C.4.2). With `z = λ σ(x) y`, it equals
`σ(z) − z`.

- `le_omega_correction`: if `ω x, ω y ≥ r`, then `ω(correction λ x y) ≥ 2r + μ`, for
  `λ = traceOneMax`.
- `le_omega_correction_of_le`: if moreover `2r = n ∈ ℤ` and `s ≤ 2r + 1/2`, then
  `ω(correction λ x y) ≥ s + μ`. This uses `traceZero_add_half_le`, exactly as in KP's proof
  of Lemma C.4.2: `ω(z − z̄) ≥ 2r + μ + 1/2 ≥ s + μ`.
- `latticeData r s : CoordinateData K L (ULift (Fin 2))` is the chart
  (`CoordinateData.ofBasis`) with basis `latticeBasis r` (reindexed by `ULift (Fin 2)`),
  trace-one element `λ = traceOneMax`, and scalar generator `f = latticeCenter s`
  (`latticeData_basis`, `latticeData_traceOne`, `latticeData_center`).
- `omega_latticeData_coeff_nonneg`: if `2r ∈ ℤ` and `s ≤ 2r + 1/2`, every cocycle
  coefficient `cᵢⱼ` of `latticeData r s` is integral. Indeed
  `cᵢⱼ · latticeCenter s = correction λ eᵢ eⱼ` with `eᵢ, eⱼ ∈ Y_r`.

The conditions `2r ∈ ℤ` and `s ≤ 2r + 1/2` are those of KP Lemma C.4.2:
`r ∈ J_{a/2a} = (1/2) ℤ` and `s ≤ 2r + 1/2`. This module does not need `s ∈ J_{2a}`. The
last result is what makes the bilinear coordinate group with these coefficients an integral
model, as the next module constructs.

## Sources

- KP, §2.8, printed pp. 110–112: (2.8.1), (2.8.2), Lemma 2.8.1.
- KP, §3.2(b), printed p. 149: (3.2.2) and Lemma 3.2.2.
- KP, Appendix C.4, printed pp. 699–701: `Y_r`, `Z_s`, (C.4.1), (C.4.2), Lemma C.4.2 and
  its proof.
