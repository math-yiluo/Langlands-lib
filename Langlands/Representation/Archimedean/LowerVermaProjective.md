# Projectivity of lower Verma modules of `𝔤𝔩_n(ℂ)`

Module `Langlands.Representation.Archimedean.LowerVermaProjective`, namespace
`Langlands.Archimedean.VermaPBW`. It imports `LowerVermaFiltration` (and through it
`LowerVermaPBW`).

The main result is `lowerVermaProjective : VermaGL.LowerVermaProjectiveStatement.{uW, uN}`. The
statement is in the Library module `LowerVerma`. Assume:

* `λ` is `Z`-extremal;
* `σ` is a finite-dimensional representation on `W` with integral weights;
* `τ` is any representation on `N`;
* `f : W ⊗ M⁻(λ) → N` is surjective and equivariant (`f(tensorEnd(σ Y, action Y) t) = τ(Y) f(t)`);
* `x ∈ N` is singular of weight `λ`: `E_pq x = 0` for `q < p` and `E_pp x = λ_p x`.

Then `x = f(t)` for some `t ∈ W ⊗ M⁻(λ)` that is itself singular of weight `λ`
(Bernstein–Gelfand 1980, 1.11 and the proof of 5.10).

## Idea

`W ⊗ M⁻(λ)` has a filtration whose successive quotients are quotients of the Verma modules
`M⁻(λ + wt(b_j))`, where `b_j` runs through a weight basis of `W`. The center acts on the `j`-th
quotient by `χ_{λ + wt(b_j)}`. There is one central element `z` with `χ_λ(z) = c₀ ≠ 0` and
`χ_{λ + wt(b_j)}(z) ∈ {0, c₀}` for all `j`. Let `t₀` be a preimage of `x` of weight `λ`. Apply
to it the projector `u = A(z) z^{D+1}` onto the generalized `c₀`-eigenspace of `z`, built from a
Bézout identity. Then `f(u t₀) = x`, and `u t₀` has weight `λ`. `Z`-extremality shows that the
`c₀`-generalized eigenvectors of weight in `λ - Q₊ ∖ {λ}` vanish. So the lowering operators
kill `u t₀`.

## 1. The tensor product representation (section `Tensor`)

* `rhoT n λ σ`: `Y ↦ σ(Y) ⊗ 1 + 1 ⊗ Y`. This is the Library's `BGChase.tensorLie σ (action n λ)`.
  `rhoT_apply`: it is `tensorEnd (σ Y) (action Y)`. `rhoT_tmul`: its value on pure tensors.
* `Gt n λ b j = b_j ⊗ gen`. `isWt_Gt`: it has weight `λ + wt(b_j)`. `tmul_eq_sum` expands
  `w ⊗ x` in the basis.
* `rhoT_Gt_lower`: for `q < p`, `E_pq (b_j ⊗ gen) = σ(E_pq) b_j ⊗ gen`, a combination of the
  `b_i ⊗ gen`.
* `Gt_lower_mem`: if `T` contains every index of smaller height than `k ∈ T`, then
  `E_pq (b_k ⊗ gen) ∈ FG (T ∖ k)`. The `b_i` that occur have smaller height
  (`wtC_eq_of_lower_coeff`, `htZ_lt_of_wtC_eq`). So `b_k ⊗ gen` is singular modulo
  `FG (T ∖ k)`, as `LowerVermaFiltration` §5 requires. Here `FG` is the filtration generated
  by the `Gt j`.
* `tmul_W_mem_FG`, `tmul_mem_FG`, `FP_univ`: `FG univ = W ⊗ M⁻(λ)`.

## 2. Central characters (section `Chi`)

* `smul_gen_inj`: scalars acting on `gen μ` are unique, since `gen μ ≠ 0` (`gen_ne_zero`).
* `chiFun`, `chiFun_spec`, `chi`, `chi_spec`: the central character `χ_μ : Z → ℂ` of `M⁻(μ)`,
  with `z • gen μ = χ_μ(z) • gen μ`, as an algebra map.
* `env_singular`: in any representation, a central `z` acts on a singular vector of weight `μ`
  by `χ_μ(z)`.
* `exists_chi_ne_of_isZExtremal`: `Z`-extremality says `χ_μ ≠ χ_λ` for `μ ∈ λ - Q₊`,
  `μ ≠ λ`.
* `aeval_apply_of_eigen`: if `T x = c x` then `p(T) x = p(c) x`.

## 3. The separating element (section `Separate`)

* `IsBad n λ m j`: `χ_{λ + wt(b_j)} ≠ χ_λ`.
* `sepFactor j` is `z_j - χ_{λ + wt(b_j)}(z_j)` for a chosen `z_j` with
  `χ_λ(z_j) ≠ χ_{λ + wt(b_j)}(z_j)` when `j` is bad, and `1` otherwise.
  `zSep = ∏_j sepFactor j`.
* `chi_zSep_ne_zero`: `c₀ = χ_λ(zSep) ≠ 0`. `chi_zSep_bad`: `χ_{λ + wt(b_j)}(zSep) = 0` for bad
  `j`. `chi_zSep_good`: it equals `c₀` for the other `j`. `chi_zSep_mem`: in all cases
  `d_j (c₀ - d_j) = 0`, where `d_j = χ_{λ + wt(b_j)}(zSep)`.

## 4. The main argument (section `Main`)

* `aeval_mem_center`, `aeval_X_sub_C`: polynomials in a central element are central, and
  `(X - c)(z) = z - c`.
* `env_prod_eq_zero`: for every downward closed `T` (closed under passing to smaller height),
  `∏_{j ∈ T} (z - d_j)` kills `FG T`. The proof is by strong induction on `T`, removing an
  index `k` of maximal height. By `FG_center_sub_mem`, `z - d_k` maps `FG T` into
  `FG (T ∖ k)`.
* `poly_factor`, `env_kill_all`: since `d_j ∈ {0, c₀}`,
  `(X - (c₀ - d_j))(X - d_j) = X (X - c₀)`. Multiplying over `j` shows that
  `(z (z - c₀))^D` kills `W ⊗ M⁻(λ)`.
* `eq_zero_of_kill`: let `T` be downward closed and `N ∈ ℕ`. Let `w ∈ FG T` have weight `ν`,
  with `λ - ν ∈ Q₊` and `ν ≠ λ`, and suppose `(z - c₀)^N w = 0`. Then `w = 0`. The proof is by
  strong induction on `T`, removing `k` of maximal height.
  - By `mem_FG_weight`, `w` lies in `FG (T ∖ k)` plus the span of the upper words `l` applied
    to `b_k ⊗ gen` with `λ + wt(b_k) + shiftOf l = ν`.
  - If such an `l` exists, then `λ - (λ + wt(b_k)) = (λ - ν) + shiftOf l ∈ Q₊`. Also
    `λ + wt(b_k) ≠ λ`, since otherwise `shiftOf l ∈ Q₊ ∩ -Q₊ = 0` (`posRootCone_antisymm`)
    and `ν = λ`. So `k` is bad by `Z`-extremality, and `d_k = 0`.
  - `FG_center_pow_sub_mem` gives `(z - c₀)^N w - (-c₀)^N w ∈ FG (T ∖ k)`, so
    `w ∈ FG (T ∖ k)`.
  - The induction hypothesis then gives `w = 0`.

## 5. Conclusion (section `Final` and `lowerVermaProjective`)

* `env_comm_central`, `isWt_env_central`: central elements commute with the action and
  preserve weights. `isWt_of_mem_span`: spans of weight-`μ` vectors have weight `μ`.
  `env_equivariant`: an equivariant linear map intertwines the enveloping actions.
  `rootOf_ne_zero`.
* **A preimage of weight `λ`.** Write `x = f(t₁)`. Split `t₁ = a + a'` along the spanning set
  of weight vectors of `FG univ = W ⊗ M⁻(λ)`, with `a` in the span of the weight-`λ`
  generators and `a'` in the span of the others. Then `f(a')` has weight `λ` and lies in the
  span of the weight vectors `f(v)` of weights `≠ λ`. So `f(a') = 0` by `mem_span_wt` and
  `isWt_unique`, and `t₀ = a` works.
* **The projector.** `X` and `X - c₀` are coprime in `ℂ[X]`, so
  `A X^{D+1} + B (X - c₀)^{D+1} = 1`. Put `u = (A X^{D+1})(zSep)`, which is central.
* `f(u t₀) = u x = (A X^{D+1})(c₀) x = x`. Here `zSep` acts on `x` by `c₀`
  (`env_singular`), and the Bézout identity evaluated at `c₀` gives `(A X^{D+1})(c₀) = 1`.
* `u t₀` has weight `λ` (`isWt_env_central`).
* For `q < p`, put `w = E_pq (u t₀) = u (E_pq t₀)`. It has weight `λ + (ε_p - ε_q)`, which lies
  in `λ - Q₊ ∖ {λ}`. Moreover
  `(z - c₀)^{D+1} u = (A X (X - c₀))(z) · (z (z - c₀))^D` kills everything
  (`env_kill_all`). Hence `w = 0` by `eq_zero_of_kill`.

## Provenance

The statement is the projectivity of the dominant Verma module in category `𝒪` used in BG
1.11 and in the proof of 5.10 (J. N. Bernstein and S. I. Gelfand, *Tensor products of finite and
infinite dimensional representations of semisimple Lie algebras*, Compositio Math. 41
(1980); literature id `bernstein-gelfand-1980-tensor-products`), for lower Verma modules of
`𝔤𝔩_n(ℂ)` with `Z`-extremal `λ`. The proof follows the standard argument (generalized central
character decomposition and the filtration of `W ⊗ M(λ)` by Verma quotients). It is written
with an explicit separating central element and a polynomial projector instead of a block
decomposition of category `𝒪`.
