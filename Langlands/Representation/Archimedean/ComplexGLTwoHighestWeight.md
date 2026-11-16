# Highest weight vectors in `(𝔤𝔩_2(ℂ), U(2))`-submodules of the principal series

Module `Langlands.Representation.Archimedean.ComplexGLTwoHighestWeight`, namespace
`Langlands.Archimedean.ComplexGLTwoNoncompact`. Internal helper module for the proof of
`ComplexGLTwoMomentCompletenessStatement` (see `ComplexGLTwoMomentCompletenessProof`).
Notation as in `ComplexGLTwoNoncompactOperators`: `X(d)` (`Xd d`), the action `π` (`πd d`),
the noncompact picture `φ_v` (`ncpL d v`), `H`, `X₊`, `p`, `q`.

## Main result

`exists_phiB_mem`: if `S ≠ 0` is a `(𝔤, K)`-submodule of `X(d)` (`IsGKSubmodule` for the
right-translation action of `U(2)` and `π`), then there are `b ∈ ℕ` and `v ∈ S` with
`φ_v = φ_b`, where

`phiB d b z = φ_b(z) = (1 + |z|²)^(-(q + 1 + b)) z̄^b`

(`pw (-(q + 1 + b)) z * conj z ^ b`; `continuous_phiB`).

## Steps

* `exists_eigen_kernel` (linear algebra): let `W ≠ 0` be a finite-dimensional subspace stable
  under endomorphisms `H`, `X` with `H X = X H + i X`. Take an eigenvalue `μ` of `H` on `W` with
  maximal imaginary part (finitely many eigenvalues, and at least one exists over `ℂ`) and an
  eigenvector `w`. If `X w ≠ 0`, it is an eigenvector of `H` with eigenvalue `μ + i`,
  contradicting maximality. So `X w = 0`.
* `exists_eH_eXp`: `S` contains `v ≠ 0` with `H v = μ v` and `X₊ v = 0`. Take `v_0 ≠ 0` in `S`;
  its `U(2)`-orbit span is finite-dimensional (the `(𝔤, K)`-module axioms of the Library's
  `isComplexGKModule_complexStandardModule`), lies in `S` and is `U(2)`-stable, hence stable
  under `H` and `X₊` (`compact_stable`). Apply `exists_eigen_kernel` with `[H, X₊] = i X₊`
  (`eH_eXp`).
* `skewExp_two_pi_Y0`: `exp(2π · i E_00) = 1` in `U(2)` (Library `skewExp`, `exp_diagI`).
* `exists_int_of_eH`: if `v ≠ 0` and `H v = μ v`, then `μ = i k` with `k ∈ ℤ`. Choose a linear
  functional `ℓ` with `ℓ(v) ≠ 0` and set `φ(t) = ℓ(ρ(exp(t i E_00)) v)`. By the Library's
  `hasDerivAt_skewExp`, `φ' = μ φ`, so `φ(t) = e^(μ t) φ(0)`
  (`OperatorRealization.eq_exp_mul_of_hasDerivAt`). Since `φ(2π) = φ(0) ≠ 0`,
  `e^(2π μ) = 1`, so `2π μ = 2π i k`.
* `differentiable_ncpL`: `φ_v` is real differentiable (Library `contDiff_apply_chart`);
  `continuous_pw`: `(1 + |z|²)^σ` is continuous.
* `ncp_highest`: if `H v = i (l_1 + b) v` (`b ∈ ℤ`) and `X₊ v = 0`, then
  `φ_v(z) (1 + |z|²)^(q + 1 + b) z̄^(-b)` is a constant `c` on `z ≠ 0`. By the operator table,
  the hypotheses read `z̄ ∂̄φ - b φ - z ∂φ = 0` and `∂φ + z̄² ∂̄φ + (q + 1) z̄ φ = 0`; combining
  them, `(1 + |z|²) ∂φ + (q + 1 + b) z̄ φ = 0`. The product rule (`HasWirt.mul`, `hasWirt_pw`,
  `HasWirt.zpow`) then shows that the product has both Wirtinger derivatives `0` at every
  `z ≠ 0`. `ℂ ∖ {0}` is open and connected (`isConnected_compl_singleton_of_one_lt_rank`), so
  the product is constant there (`IsOpen.exists_is_const_of_fderiv_eq_zero`).
* `highest_eq_phiB`: if moreover `v ≠ 0`, then `b ≥ 0` and `φ_v = c φ_b` with `c ≠ 0`. If
  `b = n ≥ 0`, `φ_v = c φ_n` on `z ≠ 0`, hence everywhere by continuity and density of
  `ℂ ∖ {0}`; `c ≠ 0` because otherwise `φ_v = 0` and `v = 0` (`ncpL_injective`). If `b = -n < 0`,
  then `φ_v(z) (1 + |z|²)^(q + 1 - n) z̄^n = c` on `z ≠ 0`; evaluating the continuous extension
  at `0` gives `c = 0`, so `φ_v = 0` on `z ≠ 0`, hence `v = 0`, a contradiction.
* `exists_phiB_mem`: by `exists_eH_eXp` and `exists_int_of_eH`, `S` contains `v ≠ 0` with
  `H v = i k v` and `X₊ v = 0`. Apply `highest_eq_phiB` with `b = k - l_1` and replace `v` by
  `c⁻¹ v ∈ S`.
