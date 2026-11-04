# A stable generating subspace of additive polynomials

Helper module for the proof of `TorusVectorActionLinearizationStatement` (task 3be1ce22).
Internal machinery only. Throughout, `k` has characteristic `p`, `K` is a field over `k`, and
`f_K` is the image of a polynomial `f` over `k` in polynomials over `K`.

- `subset_frobSpan_zero`, `frobSpan_le_frobSpan_zero`: `S ⊆ frobSpan k p 0 S`, and the
  Frobenius span from any level `m` lies in the one from level `0`.
- `spanK K W`: the `K`-span of the `f_K` with `f ∈ W`. `map_mem_spanK` and `spanK_mono` are the
  obvious facts. `pow_mem_spanK`: if `f ↦ f^p` maps `W` into `W'`, it maps `spanK K W` into
  `spanK K W'`. The proof is span induction, using additivity of the `p`-th power over `K` and
  `(c v)^p = c^p v^p`.
- `map_mem_addSpan`: `f_K ∈ addSpan n K p` when `f ∈ addSpan n k p` (supports only shrink).
- `mem_higher_of_coeff_eq_zero`: an element of `addSpan` whose coefficients at all exponents
  `single j 1` vanish lies in `higher n k p`. Each monomial of its support is a scalar multiple
  of some `X_j^(p^r)`, and `r = 0` is excluded by the vanishing coefficient.
- For a point action `a`:
  - `stable_of_le_fixed`: a subspace of the fixed polynomials is stable.
  - `isAddPoly_of_mem_fixed`, `pow_mem_fixed`: fixed polynomials are additive, and the fixed
    polynomials are closed under `f ↦ f^p` (pullback is a ring map, and the `p`-th power
    preserves `addSpan`).
  - `exists_frobBasis_fixed`: there is a finite Frobenius-independent family `G` of fixed
    polynomials with `fixed p ≤ frobSpan k p 0 G`. This is `exists_frobBasis` with
    `s = univ`.
  - Assume now `I` is finite with decidable equality, so that weight components `comp χ` are
    available.
  - `mem_frobSpan_one_of_mem_higher` (purity): if `fixed p ≤ frobSpan k p 0 G`, then every
    fixed `f` in `higher` lies in `frobSpan k p 1 G`. The weight-zero component of
    `(X_j^(p^(r+1)))_K = ((X_j^(p^r))_K)^p` is the `p`-th power of the weight-zero component of
    `(X_j^(p^r))_K` (`comp_pow_char_smul`). That component lies in the `K`-span of the fixed
    polynomials (`mem_span_fixed`), hence in `spanK K (frobSpan k p 0 G)`, and so its `p`-th
    power lies in `spanK K (frobSpan k p 1 G)`. By linearity the weight-zero component of `y_K`
    lies there for every `y ∈ higher`. For fixed `f` every nonzero weight component of `f_K`
    vanishes (`comp_map_fixed`), so `f_K` equals its weight-zero component. Descent of span
    membership (`mem_of_map_mem_span`) finishes the proof.
  - `comp_map_mem_spanK` (graded Nakayama): fix `θ` and `π'` as in `Complement` and a
    `k`-subspace `F` that contains `complement p θ π'` and `fixed p` and is closed under
    `f ↦ f^p`. Then every weight component of `f_K`, `f ∈ addSpan`, lies in `spanK K F`. The
    proof is strong induction on `∑ |χ_i|`. Weight `0` uses `mem_span_fixed`. For `χ ≠ 0`,
    write `f = l + y + z` with `l` in the complement, `y ∈ higher`, `z` fixed
    (`addSpan_le_complement_sup`). The complement part is handled by `stable_complement` and
    `comp_mem_span_of_stable`, and the fixed part has no component of weight `χ ≠ 0`. For the
    generators `X_j^(p^(r+1))` of `higher`, `comp_pow_char` writes the weight-`χ` component as
    the `p`-th power of the weight-`ψ` component of `X_j^(p^r)` when `χ = p ψ`, and as `0`
    otherwise. Here `ψ ≠ 0` and `∑ |ψ_i| < ∑ |χ_i|`, so induction and `pow_mem_spanK` apply.
  - `addSpan_le_of_frobClosed`: under the same hypotheses, `addSpan n k p ≤ F`. Since `f_K` is
    the sum of its weight components (`sum_comp`), it lies in `spanK K F`; then descend with
    `mem_of_map_mem_span`.
  - `exists_subspace`: there is a `k`-subspace `W` with `W ≤ addSpan n k p` that is stable,
    on which `w ↦ (coefficient of w at single j 1)_j` is injective, and with
    `X_j ∈ frobSpan k p 0 W` for every `j`. The proof takes `θ` from `exists_theta`, `π'` from
    `exists_projection`, `G` from `exists_frobBasis_fixed`, and
    `W := complement p θ π' ⊔ span k G`.
    - Stability: `Stable.sup` of `stable_complement` and `stable_of_le_fixed`.
    - Injectivity: write `w = l + g`, with `l` in the complement and `g ∈ span k G`, and
      suppose all linear coefficients of `w` vanish. Then `w ∈ higher`
      (`mem_higher_of_coeff_eq_zero`), so `l = w - g ∈ fixHigher p`, and
      `complement_inf_fixHigher` gives `l = 0`. Then `g` is fixed and in `higher`, so purity
      puts `g = ∑ c_x x` in `frobSpan k p 1 G`. `FrobIndep.eq_zero_of_sum_smul_mem` gives
      `c_x = 0` for every `x ∈ G`, so `g = 0`.
    - Generation: apply `addSpan_le_of_frobClosed` to `F := frobSpan k p 0 W`. It contains
      `W`, hence the complement, and contains `frobSpan k p 0 G ⊇ fixed p`. It is closed under
      `p`-th powers by `pow_mem_frobSpan_succ`. Hence `X_j = X_j^(p^0) ∈ addSpan ≤ F`.
