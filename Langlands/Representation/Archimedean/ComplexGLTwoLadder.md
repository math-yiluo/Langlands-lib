# Lowering the highest weight in the `GL_2(ℂ)` principal series

Module `Langlands.Representation.Archimedean.ComplexGLTwoLadder`, namespace
`Langlands.Archimedean.ComplexGLTwoNoncompact`. Internal helper module for the proof of
`ComplexGLTwoMomentCompletenessStatement` (see `ComplexGLTwoMomentCompletenessProof`).
Notation as in `ComplexGLTwoNoncompactOperators` and `ComplexGLTwoHighestWeight`: `X(d)`
(`Xd d`), the action `π` (`πd d`), the noncompact picture `φ_v` (`ncpL d v`), the elements
`D̄` (`eDb`), `X₋` (`eXm`) and `P` (`eP`), `p = pp d`, `q = qq d`, and
`φ_b(z) = (1 + |z|²)^(-(q + 1 + b)) z̄^b` (`phiB d b`). The lowering identity below was derived
for this proof (and checked numerically before being formalized); it is not quoted from the
literature. Its Lean proof is the direct computation described below.

## Definitions

* `mono g k a c z = (1 + |z|²)^(-g) z^a z̄^c / (1 + |z|²)^k` (with `W z = 1 + z z̄` in the
  denominator).
* `mC d = m = l_0 - l_1` (as a complex number), and `lD d n = D = 2(n + 1) - m`, i.e. `D = 2b - m`
  for `b = n + 1`.
* `pp_eq`: `p = q + m`.

## Results

* `hasWirt_W_pow_inv`: `z ↦ (1 + |z|²)^(-k)` has Wirtinger derivatives
  `(-k z̄ / W^(k+1), -k z / W^(k+1))` (from `HasWirt.zpow` applied to `hasWirt_W`).
* `hasWirt_mono`: `mono g k a c` has Wirtinger derivatives

  `∂ = (1 + |z|²)^(-g) (a z^(a-1) z̄^c / W^k - (g + k) z^a z̄^(c+1) / W^(k+1))`,
  `∂̄ = (1 + |z|²)^(-g) (c z^a z̄^(c-1) / W^k - (g + k) z^(a+1) z̄^c / W^(k+1))`

  (product rule with `hasWirt_pw`, powers of `z` and `z̄`, and `hasWirt_W_pow_inv`; the
  derivatives are rearranged with `pw_sub_one`). Natural-number subtraction is truncated, which
  is harmless because the corresponding coefficient `a` or `c` is then `0`.
* `ncpL_eXm_eq`, `ncpL_eP_eq`, `ncpL_eDb_eq`: if `φ_w = f` and `f` has Wirtinger derivatives
  `(A, B)` everywhere, then `φ_{X₋ w} = -(z² A + (p + 1) z f) - B`,
  `φ_{P w} = A - (z̄² B + (q + 1) z̄ f)` and `φ_{D̄ w} = B` (the operator table of
  `ComplexGLTwoNoncompactOperators`).
* `ncpL_ladder` (the lowering identity): let `b = n + 1`, `D = 2b - m` and
  `β = -b (b - p)(D + 2) - (b + 1 - m)(q + b + 1) D`. If `φ_v = φ_b`, then

  `φ_u = b (b - m)(b - p)(D + 2) φ_n`, where
  `u = D (D + 1)(D + 2) D̄ v - β X₋ v + (D / 2) X₋ X₋ P v`.

* `exists_phiB_pred_mem`: let `S` be a `(𝔤, K)`-submodule of `X(d)` (`IsGKSubmodule`) and
  `v ∈ S` with `φ_v = φ_(n+1)`. If `b (b - m)(b - p)(D + 2) ≠ 0` for `b = n + 1`, then some
  `w ∈ S` has `φ_w = φ_n`.

## Proofs

* `ncpL_ladder`. Put `γ = q + 1 + b`, so `φ_v = mono γ 0 0 b`. All noncompact pictures are
  computed with `ncpL_eXm_eq`, `ncpL_eP_eq`, `ncpL_eDb_eq` and `hasWirt_mono`:
  * `φ_{P v} = -2γ mono γ 1 0 (b + 1)` (the `z̄^(b+1)` terms combine because `γ = q + 1 + b`;
    closed by `field_simp` and `ring`);
  * `φ_{X₋ P v} = c₁ mono γ 2 2 (b + 2) + c₂ mono γ 1 1 (b + 1) + c₃ mono γ 1 0 b +
    c₁ mono γ 2 1 (b + 1)` with `c₁ = -2γ(γ + 1)`, `c₂ = 2γ(p + 1)`, `c₃ = 2γ(b + 1)`;
  * `φ_{X₋ X₋ P v}` by applying `ncpL_eXm_eq` once more to this sum (the derivatives of the four
    monomials are added with `HasWirt.add` and `HasWirt.const_mul`);
  * `φ_{X₋ v}` and `φ_{D̄ v}` directly from `mono γ 0 0 b`.

  Also `φ_n = (1 + |z|²)^(-γ) W z̄^n` (`pw_add_one`). After linearity of `ncpL d` and
  substitution of these formulas, both sides at each point `z` are `(1 + |z|²)^(-γ)` times a
  rational function of `z`, `z̄`, `p`, `q`, `m`, `n` with denominators powers of `W ≠ 0`; the
  common factor `(1 + |z|²)^(-γ)` is generalized to a variable, `p` is replaced by `q + m`, and
  the identity is closed by `field_simp` and `ring`.
* `exists_phiB_pred_mem`. `S` is stable under `π`, so `u ∈ S`; by `ncpL_ladder`,
  `w = c⁻¹ u ∈ S` with `c = b (b - m)(b - p)(D + 2) ≠ 0` has `φ_w = φ_n`.
