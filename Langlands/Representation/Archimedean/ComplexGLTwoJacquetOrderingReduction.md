# Reduction of the `GL_2(ℂ)` ordering of Jacquet exponents to moment integrals

Lean module: `Langlands.Representation.Archimedean.ComplexGLTwoJacquetOrderingReduction`
(namespace `Langlands.Archimedean`, universe `uV` for the module carrier).

## Notation

`d : Fin 2 → ComplexCharacterData` is a pair of complex characters. `t_k = (d k).exponent`
is the exponent of `d k` and `l_k = (d k).weight` its weight, so
`(d k).character z = (z/|z|)^{l_k} |z|^{2 t_k}`. `X(d)` is
`kFiniteFunctions (complexStandardModule 2 (List.ofFn d)) (unitaryCompact ℂ 2)`: the
`U(2)`-finite smooth functions `f` on `GL_2(ℂ)` with
`f(diag(a_0, a_1) u g) = (d 0).character(a_0) |a_0| (d 1).character(a_1) |a_1|^{-1} f(g)` for
`u` upper unipotent. The `(𝔤, K)`-module structure on `X(d)` is
`complexStandardRep 2 (List.ofFn d)` (right translation by `U(2)`) and
`complexStandardLie 2 (List.ofFn d)` (right derivatives). `R(X) f` is
`rightDerivative (matrixModel ℂ 2) X f`, the derivative of `h ↦ f(g h)` at `h = 1` in the
direction `X`.

## Definitions

* `complexGLTwoWeyl : GL_2(ℂ)` is the long Weyl element `w = [[0, 1], [1, 0]]`.
* `complexGLTwoUnipotent z : GL_2(ℂ)` is `n(z) = [[1, z], [0, 1]]` for `z : ℂ`.
* `complexGLTwoMoment i j f` is the moment
  `M_{i,j} f = ∫_ℂ f(w n(z)) z^i z̄^j dz`
  of a function `f : GL_2(ℂ) → ℂ`, for `i j : ℕ` and Lebesgue measure on `ℂ` (the Bochner
  integral, which is `0` when the integrand is not integrable).
* `complexGLTwoMomentLinear d i j hM hij` is `f ↦ M_{i,j} f` as a linear functional on `X(d)`.
  It needs `i + j < 2 Re(t_0 - t_1)` and the statement `ComplexGLTwoMomentJacquetStatement`
  (`hM`) for integrability. `complexGLTwoMomentLinear_apply` records its value.

## Statements

### `ComplexGLTwoMomentJacquetStatement` (the moments are Jacquet-type)

For all `d`, all `i j : ℕ` with `i + j < 2 Re(t_0 - t_1)`, and all `f ∈ X(d)`:

1. `z ↦ f(w n(z)) z^i z̄^j` is integrable on `ℂ`;
2. for every strictly upper triangular `X` (`X a b = 0` whenever `b ≤ a`),
   `M_{i,j}(R(X) f) = -(i X₀₁ M_{i-1,j} f + j X̄₀₁ M_{i,j-1} f)`
   (in Lean, `i - 1` and `j - 1` are truncated subtraction; the term vanishes when `i = 0`,
   resp. `j = 0`, because of the factor `i`, resp. `j`);
3. for `k = 0, 1`, with `E_kk = Matrix.single k k 1` and `i E_kk = Matrix.single k k i`,
   `M_{i,j}(R(E_kk) f) = a'_k M_{i,j} f` and `M_{i,j}(R(i E_kk) f) = b'_k M_{i,j} f`, where
   `a' = (2 t_1 + 1 + (i + j), 2 t_0 - 1 - (i + j))` and
   `b' = (i (l_1 + i - j), i (l_0 - i + j))`.

Why this is true. Write `w n(z) = β(z) k(z)` with `β(z)` upper triangular and
`k(z) ∈ U(2)`. The bottom row `(1, z)` of `w n(z)` gives `|β(z)_{11}| = (1 + |z|^2)^{1/2}`,
and `|det| = 1` gives `|β(z)_{00}| = (1 + |z|^2)^{-1/2}`. Hence
`|f(w n(z))| ≤ C (1 + |z|^2)^{-Re(t_0 - t_1) - 1}` (with `C = sup_{U(2)} |f|`), and the
integrand is integrable when `i + j < 2 Re(t_0 - t_1)`. Part 2 holds because `R(X)` for `X = x E_01` is the
derivative of `f(w n(z + τx))` in the real variable `τ`. Substituting `z ↦ z - τx` and
differentiating under the integral gives the formula. Part 3 holds because
`n(z) diag(e^τ, 1) = diag(e^τ, 1) n(e^{-τ} z)` and `w diag(α, β) = diag(β, α) w`. These
identities turn `f(w n(z) h)` for diagonal `h` into a character value times `f(w n(z'))`
with `z'` a rescaling or rotation of `z`. The change of variables in `ℂ` gives the factor
`|λ|^{2 + i + j}` for `z = λ u` with `λ > 0`, and the factor `e^{iθ(i - j)}` for the
rotation `z = e^{iθ} u`. The Jacobian of `z ↦ λ z` on `ℂ = ℝ^2` is `λ^2`. Twisting by
`z^i z̄^j` therefore moves the torus exponents by `i + j` and the weights by `±(i - j)`.
The moment `M_{0,0}` is the value at `1` of the standard intertwining integral
`A f(g) = ∫_ℂ f(w n(z) g) dz` (Wallach 1979, Lemma 7.6, printed p. 81, PDF p. 84, with
`F = ℂ`).

### `ComplexGLTwoMomentCompletenessStatement` (low moments detect submodules)

For all `d` with `Re t_1 < Re t_0` and every nonzero `(𝔤, K)`-submodule `S` of `X(d)`
(`IsGKSubmodule (complexStandardRep 2 _) (complexStandardLie 2 _) S`, `S ≠ ⊥`), there are
`i j : ℕ` and `f ∈ S` with `i + j ≤ Re(t_0 - t_1)` and `M_{i,j} f ≠ 0`.

Why this is true. Put `s = t_0 - t_1`, `m = l_0 - l_1`, `p = s + m/2`, `q = s - m/2`, so
`μ = μ_1 μ_2^{-1}` is `z ↦ z^p z̄^q` in the notation of Jacquet–Langlands 1970, §6, with
`μ_1 = d 0`, `μ_2 = d 1`. Their `B(μ_1, μ_2)` is `X(d)`: the factor `|a_0| |a_1|^{-1}` is
`|a_0/a_1|_ℂ^{1/2}`. If `M_{0,0}` vanishes on `S`, then `A f` vanishes on `U(2)` for every
`f ∈ S`, because `S` is `U(2)`-stable and `A f(k) = M_{0,0}(R(k) f)`. So `A f = 0` by the
Iwasawa decomposition, and `S ⊆ ker A`.

By Jacquet–Langlands 1970, Theorem 6.2, `X(d)` is irreducible unless `p, q` are positive
integers (the other reducible case, `p, q ≤ -1`, would force `Re s < 0`). When `X(d)` is
irreducible, `S = X(d)` and `M_{0,0} ≠ 0` on it. This is the case `(i, j) = (0, 0)`. When `p` and
`q` are positive integers, the unique proper nonzero submodule is the infinite-dimensional
`B_s(μ_1, μ_2)`. It is the kernel of `A` and the annihilator of the finite-dimensional
moments `M_{i,j}` with `i < p`, `j < q`. On it, `M_{0,q}` (if `q ≤ p`) or `M_{p,0}` (if
`p ≤ q`) is nonzero. These moments converge, since `q < p + q` and `p < p + q`. They are nonzero
on `B_s` because the function `z̄^q`, resp. `z^p`, is not a combination of the `z^i z̄^j`
with `i < p`, `j < q`. In both cases `i + j = min(p, q) ≤ (p + q)/2 = Re s`.

### `ComplexGLTwoJacquetOrderingReductionStatement`

```
def ComplexGLTwoJacquetOrderingReductionStatement : Prop :=
  ComplexGLTwoMomentJacquetStatement → ComplexGLTwoMomentCompletenessStatement →
    ComplexGLTwoJacquetOrderingStatement.{uV}
```

`ComplexGLTwoJacquetOrderingStatement` (module
`Langlands.Representation.Archimedean.ComplexGLTwoJacquetOrdering`) says that every
`(𝔤𝔩_2(ℂ), U(2))`-module with a nonzero Jacquet functional of exponents `a, b` has a
nonzero Jacquet functional of exponents `a', b'` with `a'_0 + a'_1 = a_0 + a_1` and
`Re a'_0 ≤ Re a'_1 + 2`.

## The proof (`complexGLTwoJacquetOrderingReduction`)

1. Frobenius reciprocity (`complexJacquetFrobenius`, the Library proof of
   `ComplexJacquetFrobeniusStatement` for `n = 2`) gives characters `d` with
   `a = (2 t_0 + 1, 2 t_1 - 1)` and a nonzero map `B : V → X(d)` with
   `IsComplexStandardEmbedding 2 ρ π (List.ofFn d) B`.
2. If `Re t_0 ≤ Re t_1`, then `Re a_0 = 2 Re t_0 + 1 ≤ 2 Re t_1 + 1 = Re a_1 + 2`, and
   `ℓ' = ℓ` works.
3. Otherwise `Re t_1 < Re t_0`. The range of `B` is a `(𝔤, K)`-submodule
   (`IsComplexStandardEmbedding.isGKSubmodule_range`). The `U(2)` part uses `map_rep`. The
   Lie part uses induction on tensors, writing `c ⊗ M = c • (1 ⊗ M)`, and `map_lie_one_tmul`.
   The range is nonzero because `B ≠ 0`. The completeness statement gives a moment
   `M_{i,j}` with `i + j ≤ Re(t_0 - t_1)` that is nonzero on the range. `Nat.find` picks one with
   `i_0 + j_0` minimal. By minimality, every `M_{i,j}` with `i + j < i_0 + j_0` vanishes on the
   range.
4. `ℓ' = complexGLTwoMomentLinear d i_0 j_0 ∘ B`, that is `ℓ' v = M_{i_0,j_0}(B v)`. It is
   linear because `i_0 + j_0 ≤ Re(t_0 - t_1) < 2 Re(t_0 - t_1)` makes the integrals
   converge (part 1 of the moment statement; `integral_add` and `integral_const_mul`). It
   is nonzero by the choice of `(i_0, j_0)`.
5. `ℓ'` is a Jacquet functional with exponents
   `a' = (2 t_1 + 1 + (i_0 + j_0), 2 t_0 - 1 - (i_0 + j_0))` and
   `b' = (i (l_1 + i_0 - j_0), i (l_0 - i_0 + j_0))`. `B(π(1 ⊗ X) v) = R(X)(B v)` turns the
   conditions into parts 2 and 3 of the moment statement. For strictly upper `X`, the
   right side of part 2 involves `M_{i_0 - 1, j_0}` and `M_{i_0, j_0 - 1}`, which vanish on
   the range by minimality (or carry the factor `0`).
6. `a'_0 + a'_1 = 2 t_0 + 2 t_1 = a_0 + a_1`. Also `Re a'_0 ≤ Re a'_1 + 2` is
   `2(i_0 + j_0) ≤ 2 Re(t_0 - t_1)`.

The proof uses only the standard axioms and no `sorry`.

## Provenance

This is our own reduction (provenance: derived). The moments `M_{i,j}` generalize the
standard intertwining integral of the `GL_2(ℂ)` principal series (`M_{0,0}`; Wallach 1979,
Lemma 7.6, printed p. 81, PDF p. 84; the `GL_2(ℂ)` principal series in 7.18–7.25, PDF
pp. 85–86). Twisting it by `z^i z̄^j` gives Jacquet functionals for the other Weyl
orderings. The completeness statement packages the structure of the `GL_2(ℂ)` principal
series given by Jacquet–Langlands 1970, Theorem 6.2 (retypeset p. 112, PDF p. 116), as
explained above. Neither statement appears in this form in the literature.
