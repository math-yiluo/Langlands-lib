# Nonvanishing of low moments on submodules of the `GL_2(ℂ)` principal series

Module `Langlands.Representation.Archimedean.ComplexGLTwoMomentCompletenessProof`. It proves
the Library statement `Langlands.Archimedean.ComplexGLTwoMomentCompletenessStatement` (module
`ComplexGLTwoJacquetOrderingReduction`) as the theorem

`Langlands.Archimedean.complexGLTwoMomentCompleteness : ComplexGLTwoMomentCompletenessStatement`.

## The statement

Let `d 0`, `d 1` be complex characters with exponents `t_0`, `t_1`, weights `l_0`, `l_1` and
`Re t_1 < Re t_0`. Let `S` be a nonzero `(𝔤, K)`-submodule (`IsGKSubmodule` for the
right-translation action `complexStandardRep` of `U(2)` and the Lie action
`complexStandardLie`) of the `U(2)`-finite functions `X(d)` in the standard module of
`List.ofFn d`. Then there are `i, j ∈ ℕ` and `f ∈ S` with `i + j ≤ Re(t_0 - t_1)` and
`M_{i,j} f ≠ 0`, where `M_{i,j} f = ∫_ℂ f(w n(z)) z^i z̄^j dz` (`complexGLTwoMoment`,
`w = [[0, 1], [1, 0]]`, `n(z) = [[1, z], [0, 1]]`). This is Mathlib's Bochner integral, which
is `0` for non-integrable functions, so nonvanishing needs integrability; it is supplied by the
hypothesis `Re β + k < -1` of `radInt_ne_zero`.

## Notation

From the helper modules (namespace `Langlands.Archimedean.ComplexGLTwoNoncompact`): `X(d)` is
`Xd d`, `φ_v(z) = v(w n(z))` is the noncompact picture `ncpL d v`, `s = t_0 - t_1`,
`m = l_0 - l_1`, `p = s + m/2` (`pp d`), `q = s - m/2` (`qq d`),
`φ_b(z) = (1 + |z|²)^(-(q + 1 + b)) z̄^b` (`phiB d b`), `wU` is `w` as an element of `U(2)`,
and `I(β, k) = ∫_ℂ (1 + |z|²)^β |z|^(2k) dz` (`radInt β k`).

## The helper modules

The proof is split into the following modules, each with its own Markdown file:

* `ComplexGLTwoWirtinger`: Wirtinger derivatives and the weight `(1 + |z|²)^σ`.
* `ComplexGLTwoNoncompactPicture`: the derivatives of `φ_v` along `E_01`, `E_10`, `E_00`,
  `E_11` in terms of Wirtinger derivatives.
* `ComplexGLTwoNoncompactOperators`: the operators `D̄`, `X₊`, `X₋`, `H`, `P` of
  `ℂ ⊗ 𝔤𝔩_2(ℂ)` in the noncompact picture, injectivity of `v ↦ φ_v`, the Weyl element.
* `ComplexGLTwoHighestWeight`: `exists_phiB_mem`, every nonzero submodule contains some `v` with
  `φ_v = φ_b`.
* `ComplexGLTwoWeylBound`: `weight_sub_le` (`m ≤ b` whenever `φ_v = φ_b`) and `ncpL_rho_wU_eq`
  (the noncompact picture of `ρ(w) v`).
* `ComplexGLTwoLadder`: the lowering identity and `exists_phiB_pred_mem`.
* `ComplexGLTwoRadial`: integrability and nonvanishing of `I(β, k)`.

The argument (a highest weight vector, lowered as far as possible, detected by an explicit
radial moment) was assembled for this proof from standard highest-weight techniques; it does
not follow a specific proof in the literature.

## Results of this module

* `exists_phiB_mem_stop`: if `v ∈ S` and `φ_v = φ_b`, then some `w ∈ S` has `φ_w = φ_c` with
  `c = 0`, `c = m` or `c = p` (as complex numbers).
* `moment_eq`: `M_{i,j} v = ∫_ℂ φ_v(z) z^i z̄^j dz` (by `weyl_mul_unipotent`, `w n(z)` is the
  argument used in the noncompact picture).
* `moment_phiB`: if `φ_v = φ_b`, then `M_{b,0} v = I(-(q + 1 + b), b)`.
* `moment_rho_wU`: if `φ_v = φ_b` and `c ∈ ℕ` with `c = b - m`, then
  `M_{0,c}(ρ(w) v) = (-1)^(l_0) I(-(q + 1 + b), c)` (from `ncpL_rho_wU_eq`, since
  `z^c z̄^c = |z|^(2c)`).
* `qq_re`, `pp_re`: `Re q = Re t_0 - Re t_1 - m/2` and `Re p = Re t_0 - Re t_1 + m/2`;
  `neg_qq_re_add`: `Re(-(q + 1 + b)) + c = -Re q - 1 - b + c`.

## Proofs

* `exists_phiB_mem_stop`: induction on `b`. For `b = 0` take `w = v`. For `b = n + 1`, if the
  ladder coefficient `b (b - m)(b - p)(D + 2)` (with `D = 2b - m`) is nonzero,
  `exists_phiB_pred_mem` gives `w ∈ S` with `φ_w = φ_n`, and the induction hypothesis applies.
  If it vanishes: `b ≠ 0`; `b - m = 0` gives `c = m`; `b - p = 0` gives `c = p`; and
  `D + 2 = 0` would mean `m = 2b + 2 > b`, contradicting `weight_sub_le`.
* `complexGLTwoMomentCompleteness`. Since `Re s > 0` by hypothesis, `exists_phiB_mem` and
  `exists_phiB_mem_stop` give `w ∈ S` with `φ_w = φ_b` and `b = 0`, `b = m` or `b = p`; also
  `m ≤ b` (`weight_sub_le`).
  * Case `m ≤ 0`. Take `f = w`, `(i, j) = (b, 0)`. Bound: if `b = 0`, `0 ≤ Re s`; if `b = m`,
    then `b = 0` (as `0 ≤ b = m ≤ 0`); if `b = p`, then `b = Re p = Re s + m/2 ≤ Re s`.
    Nonvanishing: `M_{b,0} w = I(-(q + 1 + b), b)` (`moment_phiB`), and `radInt_ne_zero` applies
    since `Re(-(q + 1 + b)) + b = -Re q - 1 < -1`, because `Re q = Re s - m/2 > 0`.
  * Case `m > 0`. Let `c = b - m ∈ ℕ` (`m ≤ b`). Take `f = ρ(w) w ∈ S` (`S` is `U(2)`-stable)
    and `(i, j) = (0, c)`. Bound: `b = 0` is impossible since `m ≤ b`; if `b = m`, `c = 0`; if
    `b = p`, `c = Re p - m = Re s - m/2 ≤ Re s`. Nonvanishing:
    `M_{0,c}(ρ(w) w) = (-1)^(l_0) I(-(q + 1 + b), c)` (`moment_rho_wU`); `(-1)^(l_0) ≠ 0`, and
    `radInt_ne_zero` applies since `Re(-(q + 1 + b)) + c = -Re q - 1 - m < -1`, because
    `Re q + m = Re s + m/2 > 0`.
