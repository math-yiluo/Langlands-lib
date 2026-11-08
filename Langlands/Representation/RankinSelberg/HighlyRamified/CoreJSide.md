# The value of the dual integral of a candidate test function

Internal helper for the proof of `HighlyRamifiedGammaStabilityStatement`. It evaluates the
integral `J` of Jacquet–Shalika 1985, §4.4 (printed pages 328–330: the reduction (5)–(12),
the relation `J_i = c W_(i,0)(e)` on printed page 329, and the equality `J₁ = J₂ ≠ 0` on
printed page 330). This is the dual corank-one integral of the candidate
test function `F_c(y) = χ(det y) Σ_z Φ(z) W(y w n(z))` (`candidateTest`, DualValue) against the
second dual `f̃'` of the test vector. The canonical structures are local instances.

- `jFactor F s A = |det A|⁻¹ |det A|^s`, built from the published density
  `lowerBlockQuotientDensity` of the lower-block chart. It is left `N`-invariant
  (`jFactor_unipotent`) and right `GL_(m+1)(O)`-invariant (`jFactor_mul_integral`), and it equals
  `1` where `ord det = 0` (`jFactor_of_ord_zero`).
- `whittaker_dualConj_principal`: `Ξ(A) = W(M(diag(A,1)))` is right invariant under the
  principal congruence subgroup of level `f`. By `whittaker_dualConj_firstColumn`
  (DualEquivariance), `Ξ(A l) = ω(l₀₀)⁻¹ Ξ(A)`, and `ω(l₀₀) = 1` because `l₀₀ ∈ 1 + 𝔭^f`
  (`firstEntry_mul_principal`).

## The evaluation

`dual_integral_value`: there is `C' > 0`, depending only on the rank and the Haar measure `η`, with
the following property. Take the data of `dual_integral_reduction` (DualReduction): a level-`f`
function `W` with central character `ω`, test data `T, Φ` with
`Φ̂(ξ) = S₁(ξ₀) S₂(ξ_tail)` on integral `ξ`, the support conditions on `S₁, S₂`, the weight
`η` of `f̃'` under `diag(I, c)`, and `S₁(c) χ(c)⁻¹ η(c) = 1_(O^×)(c)`. Let `U` be a smooth Whittaker
function on `GL_(m+2)` with

`∫ S₂(rev x) f̃'([[A,0],[x,1]]) dx = χ(det A) U(diag(A,1))`

for all `A`. Assume that the weighted `K⁰(f)`-average of `F_A = corankRestriction U`
(ShellDischarge) is `c₀` times the target `t` (DualTarget). Then, for every `s` at which the
dual integrand is measurable and integrable,

`J(s) = C' χ(det w) c₀ W(1)`.

Proof.
1. `dual_integral_reduction` writes `J(s)` as `C' ∫_q density(q) ∫_x (integrand at (q, x, 1))`.
2. `dual_inner_integral` evaluates each inner integral at a representative `A = q.out` of `q`.
   The hypothesis on `U` and `|det A|^(s-1/2) = |det A|^s |det A|^(-1/2)` (`Complex.cpow_add`)
   turn the outer integrand into `Ξ(A) F_n(A)` with `F_n = χ(det w) jFactor(s) F_A`. The
   integrability of `Ξ F_n` is that of the reduced integrand.
3. `dual_pairing_of_average_eq_target` (DualJValue) applies to `Ξ` and `F_n`. The equivariance
   of `Ξ` under `K⁰(f)` is `whittaker_dualConj_firstColumn`, and that under `N` is
   `whittaker_dualConj_unipotent` (CoreAnalytic). `F_n(u A) = ψ_N(u) F_n(A)` holds because
   `jFactor` is `N`-invariant. The weighted average of `F_n` at `g` equals `χ(det w) jFactor(g)`
   times that of `F_A`: on `K⁰(f) ⊆ GL_(m+1)(O)` the factor is invariant (`rightAverage_apply`,
   `integral_const_mul`). The target is supported on `ord det = 0`
   (`firstColumnTarget_ord_det`), where `jFactor = 1`. So the average of `F_n` is
   `χ(det w) c₀ t`.
4. Hence `∫ Ξ F_n = χ(det w) c₀ Ξ(1)` with `Ξ(1) = W(1)`.
