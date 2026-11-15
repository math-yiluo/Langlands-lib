# Casselman's vanishing argument for an abstract family of matrix coefficients

Module: `Langlands.Representation.Archimedean.RealJacquetGronwall` (namespace
`Langlands.Archimedean.RealJacquetGronwall`).

Main theorems: `Langlands.Archimedean.RealJacquetGronwall.decay` and
`Langlands.Archimedean.RealJacquetGronwall.eq_zero`.

## Purpose and provenance

This is a helper module for the proof of
`Langlands.Archimedean.RealJacquetNonvanishingSubquotientReductionStatement`
(module `RealJacquetNonvanishingProof`). It is the core of Casselman's argument that
`V ≠ 𝔫V` (Wallach 1979, 4.13), axiomatized over an abstract family of bilinear forms. The
formulation is internal to this formalization. It replaces the asymptotic expansions of
matrix coefficients used in the literature (Casselman–Miličić) by two estimates: decay from
`V = 𝔫^k V`, and a Gronwall bound for the first-order system that the radial finiteness
(`RealJacquetRadialFiniteness`) provides.

## Setting

`(π, V)` is a `ℂ ⊗_ℝ 𝔤𝔩_n(ℝ)`-module, `P` a complex vector space,
`ℓ : ℝ → P →ₗ V →ₗ ℂ` a family of bilinear forms, `R : Fin n → Fin n → P →ₗ P`, and
`h : Fin n → ℝ`. Here `op π X = π(1 ⊗ X)` and `E a b` is the matrix unit. The hypotheses used
below are:

- (`hh`) `h a - h b ≤ -1` whenever `a < b`;
- (`hadj`) `ℓ s ψ (op π (E a b) v) = -e^{s (h_a - h_b)} · ℓ s (R a b ψ) v`;
- (`hgrowth`) for every `ψ, v` there is `C` with `‖ℓ s ψ v‖ ≤ C e^{c s}` for `s ≥ 0`; the
  exponent `c` is fixed;
- (`htop`) `realJacquetSubspace n π = ⊤`, i.e. `𝔫V = V`;
- (`hderiv`) `s ↦ ℓ s ψ v` has derivative `ℓ s ψ (op π (diag h) v)`;
- (`hinf`) `π` has an infinitesimal character.

## Declarations

### Decay (section `Decay`)

- `decaySpace ℓ c k`: the vectors `v` such that for every `ψ` there is `C` with
  `‖ℓ s ψ v‖ ≤ C e^{(c - k) s}` for `s ≥ 0`. It is a subspace.
- `exp_mul_sub_le`: `e^{s (h_a - h_b)} ≤ e^{-s}` for `a < b`, `s ≥ 0`.
- `decay`: under `hh`, `hadj`, `hgrowth`, `htop`, `decaySpace ℓ c k = ⊤` for every `k`.
  Induction on `k`: `k = 0` is `hgrowth`. For the step, `realJacquetSubspace` is spanned by
  vectors `op π X v` with `X` strictly upper triangular. Expanding `X` in matrix units
  (`op_eq_sum`), each term `op π (E a b) v` with `a < b` is bounded through `hadj` by
  `e^{-s} · C e^{(c - k) s}`.

### Bounded functions (section `Bounded`)

For finite families `bB : Fin m → V`, `bΨ : Fin p → P` and `s₀ : ℝ`:

- `normSum ℓ bB bΨ t = ∑_{i,j} ‖ℓ t (bΨ j) (bB i)‖` (`normSum_nonneg`, `norm_le_normSum`).
- `boundedSpace ℓ bB bΨ s₀`: the functions `f : [s₀, ∞) → V` with
  `‖ℓ q (bΨ j) (f q)‖ ≤ C · normSum q` for some `C` and all `q, j`. It is a subspace.
- `bound_of_mem_span`, `bound_of_mem_span_family`: the same bound holds for every `ψ` (or
  finite family of `ψ`'s) in the span of `bΨ`.
- `constMap_mem_boundedSpace`: constant functions with values in the span of `bB` are in
  `boundedSpace`.

### Radial stability (section `Radial`)

- `radialParam h s₀ q a b = e^{q (h_a - h_b)}`. For `a < b` and `s₀ > 0`, `radialParam_le`
  gives `radialParam ≤ e^{-s₀}`, `radialParam_lt_one` gives `radialParam < 1`, and
  `radialParam_sq_ne_one` gives `radialParam² ≠ 1`.
- `isRadialStable_boundedSpace`: assume `hh`, `s₀ > 0`, `hadj`, and that the span of `bΨ`
  contains `R a b ψ - R b a ψ` for every `ψ` in it. Then `boundedSpace ℓ bB bΨ s₀` is
  `RealJacquetRadial.IsRadialStable π (radialParam h s₀)`. With `r = e^{q (h_a - h_b)}`,
  `hadj` and `r² · e^{q (h_b - h_a)} = r` give
  `ℓ q ψ ((E_{ab} - r² E_{ba}) x) = -r · ℓ q (R a b ψ - R b a ψ) x` (`linear_combination`).
  Then `r ≤ 1`, `r² ≤ 1` and `(1 - r²)⁻¹ ≤ (1 - e^{-2 s₀})⁻¹` bound the three operations.

### Box vectors (section `Box`)

- The reused `RealJacquetFiniteGeneration.le_boxSpace` gives `F ≤ boxSpace π F`
  (the exponent `0`); its proof is in `RealJacquetFiniteGenerationProof`.
- `constMap_op_mem`: under the hypotheses of `radial_finiteness`, `constMap (op π Y u) ∈ S` for
  every `u ∈ boxSpace π F` and every `Y`. The box space is a sum of the images
  `diagEval π (monomial β 1) F`, and `op π Y` of such a vector is a word applied to `f ∈ F`
  (`exists_list_of_monomial`, `wordOp_map_D`).

### Vanishing (section `Vanishing`)

- `span_range_coe_basis`: a submodule is contained in the span of the coerced vectors of any
  of its bases.
- `eq_zero`: assume `hinf`, `hh`, `hadj`, `hderiv`, `hgrowth`, `htop`, a finite-dimensional
  `F ⊆ V` stable under `op π Y` for antisymmetric `Y`, and a finite family `bΨ` whose span is
  stable under `R a b - R b a`. Then `ℓ s₀ ψ v = 0` for every `s₀ > 0`, every `ψ` in the span of
  `bΨ`, and every `v ∈ F`.

## Proof of `eq_zero`

Let `bB` be the vectors of a basis of the box space `boxSpace π F`.

1. `boundedSpace ℓ bB bΨ s₀` is radially stable and contains the constant box vectors, so by
   `constMap_op_mem` there is `C_H` with
   `‖ℓ q (bΨ j) (op π (diag h) (bB i))‖ ≤ C_H · normSum q` for all `q ≥ s₀`.
2. Let `Φ(t) = (ℓ t (bΨ j) (bB i))_{i,j}` with the sup norm. By `hderiv` (componentwise,
   `hasDerivAt_pi`), `Φ' = (ℓ t (bΨ j) (op π (diag h) (bB i)))`. Since
   `normSum ≤ m p ‖Φ‖`, `‖Φ'(t)‖ ≤ K ‖Φ(t)‖` for `t ≥ s₀`, with `K = |C_H| m p`.
3. Gronwall backwards: apply `norm_le_gronwallBound_of_norm_deriv_right_le` to
   `u ↦ Φ(s₀ + T - u)` on `[s₀, T]` (derivative by `HasDerivAt.comp_const_sub`). This gives
   `‖Φ(s₀)‖ ≤ ‖Φ(T)‖ e^{K (T - s₀)}` (`gronwallBound_ε0`).
4. Decay: choose `k > c + K + 1` (`exists_nat_gt`). By `decay`,
   `‖Φ(T)‖ ≤ A e^{(c - k) T}` for `T ≥ s₀`. Hence `‖Φ(s₀)‖ ≤ A e^{-K s₀} e^{-T}` for all
   `T ≥ s₀`, and letting `T → ∞` (`ge_of_tendsto`, `Real.tendsto_exp_neg_atTop_nhds_zero`)
   gives `Φ(s₀) = 0`.
5. `v ∈ F ⊆ boxSpace π F` and `ψ` are linear combinations of the `bB i` and `bΨ j`, so
   `ℓ s₀ ψ v = 0` by bilinearity.
