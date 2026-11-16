# Landing of composites of block Fourier multipliers on `GL_3(ℝ)`

Lean module: `Langlands.Representation.Archimedean.RealSwapLandingStatement`
(namespace `Langlands.Archimedean`).

Worker 763 wrote this module for Task 7133 (`534c17c3-0cef-4982-b771-0750d513e885`), the proof of
`Langlands.Archimedean.RealCharacterInducedFiltrationStatement` (module
`RealInducedPairFiltrationReduction`). The mirror Task 7134 (`adfadcc2-a871-435c-ac94-9ab97d899a00`)
uses the same statements. The module defines three propositions and proves nothing.

## Notation

These are the Library's definitions; nothing new is defined here except the three propositions.

* `GL_3(ℝ)` is `Langlands.GeneralLinear 3 ℝ` and `O(3)` is its subgroup `unitaryCompact ℝ 3`.
* `r_p(θ) = blockRotation 3 p θ`: the rotation by `θ` in the coordinates `p, p + 1`
  (Library module `RealBlockRotation`, `blockRotation_val_eq`). So `r_0` acts on the coordinates
  `0, 1` and `r_1` on the coordinates `1, 2`.
* `Φ^p_k F (g) = blockFourierCoefficient 3 p k F g = ∫₀^{2π} F(r_p(θ) g) e^{-ikθ} dθ`, the
  left Fourier coefficient of weight `k` of `F : GL_3(ℝ) → ℂ` along `r_p`, at `g`.
* `c : RealCharacterData` is a character `sgn^ε₁ |·|^s` of `ℝˣ`, with parity
  `ε₁ = c.parity.val ∈ {0, 1}`. `d : ComplexCharacterData` has weight `m = d.weight` and
  exponent `t`; `ℓ = |m| = d.weight.natAbs`.
* `realStandardModule 3 [RealBlock.induced d, RealBlock.character c]` is the standard module of
  `[d, c]`: the functions of the principal series of the characters
  `(sgn^{ℓ+1} |·|^{t+ℓ/2}, |·|^{t-ℓ/2}, c)` of the diagonal torus whose coefficients `Φ^0_k`
  vanish everywhere for `|k| < ℓ`. `realStandardModule 3 [RealBlock.character c, RealBlock.induced d]`
  is the standard module of `[c, d]`: principal series of `(c, sgn^{ℓ+1} |·|^{t+ℓ/2}, |·|^{t-ℓ/2})`
  with `Φ^1_k = 0` for `|k| < ℓ`. `kFiniteFunctions V (unitaryCompact ℝ 3)` is the subspace
  of right `O(3)`-finite functions of `V`.
* `RealBlockMultiplier.IsRecurrent δ ε μ`: `μ (k + 2) (δ + k) = (k + 2 - δ) μ k` for all
  `k ≡ ε (mod 2)`. `RealBlockMultiplier.IsSymmetric ε σ μ`: `μ (-k) = σ μ k` for all
  `k ≡ ε (mod 2)`. Both depend only on the parity class of `ε`.
* `ε₀ = ℓ + 1 + ε₁`, used as a parity class (it is the natural number
  `d.weight.natAbs + 1 + c.parity.val`, not reduced modulo `2`). The symmetry signs are
  `σ₁ = (-1)^ε₁` and `σ₀ = (-1)^ε₀`. The representatives in `{0, 1}` of the two classes are
  `e₁ = ε₁` and `e₀ = ε₀ mod 2`; they are used only in the explanations below.

## The statements

`RealSwapLandingInducedFirstStatement`: for all `c`, `d`, every `δ ∈ ℂ`, all `μ₀, μ₁ : ℤ → ℂ`
and all `f, h, u : GL_3(ℝ) → ℂ` such that

1. `IsRecurrent δ ε₁ μ₁` and `IsSymmetric ε₁ σ₁ μ₁`;
2. `IsRecurrent (δ + ℓ) ε₀ μ₀` and `IsSymmetric ε₀ σ₀ μ₀`;
3. `f` is a right `O(3)`-finite function of the standard module of `[d, c]`;
4. `h` and `u` are continuous;
5. `Φ^1_k h (g) = μ₁ k · Φ^1_k f (g)` for every `g ∈ O(3)` and every integer `k`;
6. `Φ^0_k u (g) = μ₀ k · Φ^0_k h (g)` for every `g ∈ O(3)` and every integer `k`;

we have `Φ^1_k u (g) = 0` for every `g ∈ O(3)` and every integer `k` with `|k| < ℓ`.

`RealSwapLandingCharacterFirstStatement`: the same with the roles of the two rotations
exchanged. Here `f` is a right `O(3)`-finite function of the standard module of `[c, d]`,
`IsRecurrent δ ε₀ μ₀`, `IsSymmetric ε₀ σ₀ μ₀`, `IsRecurrent (δ + ℓ) ε₁ μ₁`,
`IsSymmetric ε₁ σ₁ μ₁`, `h`, `u` are continuous,
`Φ^0_k h = μ₀ k · Φ^0_k f` and `Φ^1_k u = μ₁ k · Φ^1_k h` on `O(3)`. The conclusion is
`Φ^0_k u = 0` on `O(3)` for `|k| < ℓ`.

`RealSwapLandingStatement` is the conjunction of the two.

Remarks on the hypotheses.

* Only values on `O(3)` enter hypotheses 5 and 6 and the conclusion; for `g ∈ O(3)` all points
  `r_p(θ) g` lie in `O(3)`. A continuous function on `O(3)` is determined by its coefficients
  `Φ^p_k` along one rotation, so `h` and `u` are determined on `O(3)` by `f`, `μ₁` and `μ₀`.
  Nothing is said about `h` and `u` off `O(3)`. Such `h` and `u` exist (for instance the block
  Frobenius maps of the Library module `RealBlockFrobeniusMap` have exactly these coefficients
  on `O(n)`), but existence is not part of the statements.
* The parity classes are those of the modes that actually occur. In the principal series of
  `[d, c]`, left translation by `r_1(π) = diag(1, -1, -1)` multiplies `f` by `c(-1) = (-1)^ε₁`, so
  `Φ^1_k f = 0` unless `k ≡ ε₁`. The function `h` is, on `O(3)`, the restriction of a function
  of the principal series of `(sgn^{ℓ+1} |·|^{t+ℓ/2}, c, |·|^{t-ℓ/2})`, where
  `r_0(π) = diag(-1, -1, 1)` acts by `(-1)^{ℓ+1} c(-1) = (-1)^ε₀`. The values of `μ₁` and
  `μ₀` off these classes therefore play no role.
* The sign `σ = (-1)^ε` is the one for which a multiplier map along `r_p` goes to the principal
  series with the two characters of the block exchanged and their signs kept. With
  `σ = -(-1)^ε` the target would have both signs twisted by `sgn`. In `IsBlockFrobData`
  (Library module `RealBlockFrobeniusMap`), these are the fields `sym`, `sign_p` and `sign_q`.
* `δ` is an arbitrary complex number; it is not tied to the exponents `s, t`. In the
  applications `δ = t - ℓ/2 - s + 1` (the recurrence parameter of the multiplier map from
  `[d, c]` along `r_1`, so that `δ + ℓ = t + ℓ/2 - s + 1` is the one of the next map along
  `r_0`) or `δ = s - t - ℓ/2 + 1` (from `[c, d]` along `r_0`, then `δ + ℓ = s - t + ℓ/2 + 1`
  along `r_1`). The decoupled form is equivalent to the coupled one, because the maps on `O(3)`
  do not see the exponents: an `O(3)`-finite function of one standard module agrees on `O(3)`
  with one of the standard module with the same `ℓ`, the same parities and any other exponents.
  The decoupled form also gives multiplier maps between the two standard modules that are
  injective and commute with `O(3)` (take `δ` non-integral with `re δ > 1`, where
  `RealBlockMultiplier.genericMultiplier` has no zeros).
* For `ℓ = 0` the conclusions are empty.

## Why the statements hold

This module proves none of the following. The section explains why the propositions are
true. Separately submitted modules implement a proof along these lines, and their own Markdown
files describe it in detail: `RealSwapLandingAlgebra` (the polynomial continuation below),
`RealSwapLandingIntegral` (the integral at the special parameters, theorem
`RealSwapLandingIntegral.inducedFirst`) and `RealSwapLandingMirror` (the second statement from
the first, theorem `RealSwapLandingMirror.characterFirst_of_inducedFirst`).

**Parity classes.** The hypotheses on `μ₁` and `μ₀` depend on `ε₁` and `ε₀` only through their
classes modulo `2`. The modes of the class with representative `e ∈ {0, 1}` are the integers
`±(e + 2m)`, `m ∈ ℕ`. The windows of modes and the base points of the multipliers below always
use the representatives `e₁ = ε₁` and `e₀ = ε₀ mod 2`. The unreduced number `ε₀` would not do:
for `ℓ = 1` and `ε₁ = 1` one has `ε₀ = 3`, and the modes `ε₀ + 2m` miss the modes `±1` of the
class.

**The intertwining integral at the special parameters.** Let `n ∈ ℕ` and `δ = n + 2`. First
replace the exponent `s` of `c` by `t - ℓ/2 - (n + 1)`, keeping its parity, and replace `f` by
the `O(3)`-finite function of the new standard module that agrees with `f` on `O(3)` (see
**Decoupling** below). For `ℓ = 0` there is nothing to prove, so let `ℓ > 0`. Let `w` be the
permutation matrix with `w e_0 = e_2`, `w e_1 = e_0`, `w e_2 = e_1`, and
`n̄(x, y) = 1 + x E_{20} + y E_{21}`. For `f` in the principal series of
`(sgn^{ℓ+1} |·|^a, |·|^b, c)` with `a = t + ℓ/2`, `b = t - ℓ/2` and `re (b - s) > 0` (here
`b - s = n + 1`), the integral `(I f)(g) = ∫_{ℝ²} f(n̄(x, y) w g) dx dy` converges absolutely.
Two facts give the landing.

* `w r_1(θ) w⁻¹ = r_0(θ)`, and `n̄(v) r_0(θ) = r_0(θ) n̄(v R_θ)` for `v = (x, y)` and the
  rotation matrix `R_θ` of `r_0(θ)` in the coordinates `0, 1`. So
  `(I f)(r_1(θ) g) = ∫ f(r_0(θ) n̄(v) w g) dv` after the measure-preserving change of variables
  `v ↦ v R_θ`, and `Φ^1_k (I f)(g) = ∫ Φ^0_k f (n̄(v) w g) dv`. If `f` is in the standard module
  of `[d, c]`, the coefficients `Φ^0_k f` vanish everywhere for `|k| < ℓ`, so `Φ^1_k (I f) = 0`
  everywhere for `|k| < ℓ`.
* `n̄(x, y) w = n̄_1(y) w_1 n̄_0(x) w_0`, with `w_p` the transposition of the coordinates
  `p, p + 1` and `n̄_p(x) = 1 + x E_{p+1,p}`. So `I = J_0 ∘ J_1` (Fubini), where `J_p` is the
  rank-one intertwining integral along the block `p, p + 1`. Writing `n̄_p(x) w_p` as an upper
  triangular matrix times `r_p(θ(x))`, `θ ∈ (0, π)`, gives
  `(J_p F)(g) = ± ∫₀^π sin^{δ_p - 2} θ F(r_p(θ) g) dθ`, a left convolution along `r_p`, with
  `δ_1 = b - s + 1 = δ` and `δ_0 = a - s + 1 = δ + ℓ`. It multiplies `Φ^p_k` by
  `± ĉ_{δ_p - 2}(k)`, where `ĉ_r(k) = ∫₀^π sin^r θ e^{ikθ} dθ`. Integration by parts gives
  `ĉ_r(k + 2)(r + 2 + k) = (k - r) ĉ_r(k)`, which is `IsRecurrent (r + 2)`, and `θ ↦ π - θ`
  gives `ĉ_r(-k) = (-1)^k ĉ_r(k)`.

At the two base points, `ĉ_r(0) = ∫₀^π sin^r θ dθ > 0`, and the imaginary part of `ĉ_r(1)` is
`∫₀^π sin^{r+1} θ dθ > 0`. So the multipliers `ĉ_n` (along `r_1`) and `ĉ_{n+ℓ}` (along `r_0`) are
nonzero at the base points `e₁` and `e₀` of their classes. They can vanish at other modes of the
class: `ĉ_1(3) = ∫₀^π sin θ e^{3iθ} dθ = 0`. Hence, for `δ = n + 2`, the statement holds for the
multipliers `μ₁ = ĉ_n`, `μ₀ = ĉ_{n+ℓ}` and `h = ± J_1 f`, `u = ± J_0 J_1 f`.

**All recurrent multipliers on a window.** Fix `e ∈ {0, 1}`, `M ∈ ℕ` and `δ ∈ ℂ`, and consider
the window of modes `e + 2m`, `0 ≤ m ≤ M`. The relations
`μ(e + 2m + 2)(δ + e + 2m) = (e + 2m + 2 - δ) μ(e + 2m)` for `m < M` are `M` bidiagonal linear
equations in the `M + 1` window values. A coefficient `δ + e + 2r` vanishes only if
`δ = -(e + 2r) ≤ 0`, and a coefficient `e + 2m + 2 - δ` only if `δ = e + 2m + 2 ≥ 2`. So for a
given `δ` at most one of the two kinds vanishes, and the equations have rank `M`: if no
`δ + e + 2r` vanishes, solve forward from `m = 0`; otherwise solve backward from `m = M`. The
solutions of this truncated system form the line spanned by
`P_δ(e + 2m) = ∏_{r<m} (e + 2r + 2 - δ) · ∏_{m≤r<M} (δ + e + 2r)`, whose entries are
polynomials in `δ`. Consequently every solution `μ` of `IsRecurrent δ e` satisfies
`μ(e + 2m) = c · P_δ(e + 2m)` on the window for some scalar `c`, and `c ≠ 0` if `μ(e) ≠ 0`.
The scalar `c` can be zero, because a solution of the full recurrence also satisfies the
relations beyond the window. For example, for `δ = -2` and `e = 0` the relation at `k = 2`
reads `μ(4) · 0 = 6 μ(2)`, so `μ(2) = 0`, and the relation at `k = 0` then gives `μ(0) = 0`.
On the window `M = 1` every such restriction is therefore `0`, although the truncated system
has the nonzero solution `P_{-2} = (-2, 4)`. A symmetry `μ(-k) = σ μ(k)` extends the
description to the negative modes of the window.

**The landing polynomial.** Fix `f`, a point `g ∈ O(3)` and `k` with `|k| < ℓ`. Since `f` is
`O(3)`-finite, there is a bound `M₁`, depending only on `f`, such that on `O(3)` only modes
`|i| ≤ e₁ + 2M₁` occur in the expansion of `f` along `r_1`. There is a bound `M₀` with the same
property for the expansions along `r_0` of the projections `Φ^1_i f`. A continuous function is
determined by its Fourier coefficients along a rotation. So hypotheses 5 and 6 determine `h` and
`u` on `O(3)`, and
`Φ^1_k u (g) = (2π)^{-2} Σ_j μ₀(j) Σ_i μ₁(i) Φ^1_k Φ^0_j Φ^1_i f (g)`, summed over the two
windows. The terms with `i` off the class `e₁`, and those with `j` off the class `e₀`, vanish
by the parity remark above. Substitute the window description, with class `e₁` and parameter
`δ` for `μ₁` and class `e₀` and parameter `δ + ℓ` for `μ₀`. This gives
`Φ^1_k u (g) = (2π)^{-2} c₀ c₁ L(δ)`, where `c₁`, `c₀` are the scalars of `μ₁`, `μ₀`. The
polynomial `L` depends only on `f`, `k`, `g` and the windows, not on `δ`, `μ₀`, `μ₁`, `h` or
`u`. Its coefficients involve only the values of `f` on `O(3)`. At `δ = n + 2` with the
multipliers of the integral, the left side is `0` and `c₀ c₁ ≠ 0`, because their values at `e₀`
and `e₁` are nonzero. So `L(n + 2) = 0` for every `n ∈ ℕ`, and `L = 0`. Hence `Φ^1_k u (g) = 0`
for every `δ` and every pair `(μ₁, μ₀)` satisfying the hypotheses, whether or not `c₀ c₁`
vanishes.

**Decoupling.** For `δ = n + 2`, replace the exponent `s` of `c` by `t - ℓ/2 - δ + 1`, keeping
its parity, and replace `f` by the `O(3)`-finite function of the new standard module that agrees
with `f` on `O(3)`. It is obtained by extension from `O(3)` with the Iwasawa decomposition
(Library module `PrincipalSeriesExtension`). The forbidden modes vanish on all of `GL_3(ℝ)`
because they vanish on `O(3)` (Library module `RealBlockPositionData`,
`mem_realStandardModule_of_unitaryCompact`). Nothing in hypotheses 5 and 6, in the conclusion or
in the coefficients of `L` changes.

**The second statement** follows from the first by a symmetry of `O(3)` combined with a sign
twist. Let `κ₀ = diag(1, -1, 1) J`, where `J` is the antidiagonal permutation matrix. It is an
orthogonal involution with `κ₀ r_0(θ) = r_1(θ) κ₀` and `κ₀ r_1(θ) = r_0(θ) κ₀` (same angle), and
`κ₀ diag(s₀, s₁, s₂) = diag(s₂, s₁, s₀) κ₀` for sign matrices. Composition with `κ₀` alone
does not give the right target model. It reverses the signs: for `f` in the principal series of
`[c, d]`, the function `x ↦ f(κ₀ x)` transforms under `diag(s₀, s₁, s₂)` by `s₂^{ε₁} s₁^{ℓ+1}`.
The principal series of `[d, c']`, for a real character `c'` of parity `ε'`, requires
`s₀^{ℓ+1} s₂^{ε'}`. These differ when `ℓ` is even. The determinant sign repairs this. The
function `F(x) = f(κ₀ x) · sgn det(κ₀ x)^{ℓ+1}` transforms by
`s₂^{ε₁} s₁^{ℓ+1} (s₀ s₁ s₂)^{ℓ+1} = s₀^{ℓ+1} s₂^{ε₁+ℓ+1}`. This is the sign character of
`[d, c']` for `ε' = (ℓ + 1 + ε₁) mod 2` and any exponent of `c'`. Since `det r_p(θ) = 1`,
`Φ^0_j F (x) = sgn det(κ₀ x)^{ℓ+1} Φ^1_j f (κ₀ x)` and
`Φ^1_j F (x) = sgn det(κ₀ x)^{ℓ+1} Φ^0_j f (κ₀ x)`. Hence the extension of `F|_{O(3)}` to the
principal series of `[d, c']` is an `O(3)`-finite function of its standard module. The functions
`h` and `u`, transformed in the same way, satisfy hypotheses 5 and 6 of the first statement for
`c'`, `d` and the same `δ`, with `μ₀` along `r_1` and `μ₁` along `r_0`. The classes match: the
class `ε'` of `c'` is that of `ε₀`, and `ℓ + 1 + ε'` has the parity of `ε₁`, with the same
symmetry signs. The conclusion of the first statement at `κ₀ g` reads
`sgn det(g)^{ℓ+1} Φ^0_k u (g) = 0`, which is the conclusion of the second.

## Use

In the proof of `RealCharacterInducedFiltrationStatement` (and of its mirror
`RealInducedCharacterFiltrationStatement`), the two standard modules of `[d, c]` and `[c, d]`
must be connected by intertwiners. The multiplier maps along one block are not enough. The
composite of a map along `r_1` and then along `r_0`, or along `r_0` and then along `r_1`, lands
in the other standard module exactly by these statements. Used with degenerate (tail)
multipliers, an uncertainty principle on `O(3)` (`RealOrthogonalBlockUncertaintyStatement`,
Library module `RealOrthogonalUncertaintyStatement`) and a count of `O(3)`-types, this gives
the surjections at the integral points where the standard module is irreducible.

## Provenance

Internal and derived. No literature source is claimed and none is formalized. The argument in
"Why the statements hold" is the classical factorization of the long intertwining integral of
the principal series into rank-one integrals, specialized to `GL_3(ℝ)` and to block Fourier
coefficients. The statements were designed for the `GL_3(ℝ)` argument above.
