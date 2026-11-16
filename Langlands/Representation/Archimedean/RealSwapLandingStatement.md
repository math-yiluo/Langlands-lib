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
  `d.weight.natAbs + 1 + c.parity.val`). The symmetry signs are `σ₁ = (-1)^ε₁` and
  `σ₀ = (-1)^ε₀`.

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
  Frobenius maps of Task 7067, module `RealBlockFrobeniusMap`, have exactly these coefficients
  on `O(n)`), but existence is not part of the statements.
* The parity classes are those of the modes that actually occur. In the principal series of
  `[d, c]`, left translation by `r_1(π) = diag(1, -1, -1)` multiplies `f` by `c(-1) = (-1)^ε₁`, so
  `Φ^1_k f = 0` unless `k ≡ ε₁`. The function `h` is, on `O(3)`, the restriction of a function
  of the principal series of `(sgn^{ℓ+1} |·|^{t+ℓ/2}, c, |·|^{t-ℓ/2})`, where
  `r_0(π) = diag(-1, -1, 1)` acts by `(-1)^{ℓ+1} c(-1) = (-1)^ε₀`. The values of `μ₁` and
  `μ₀` off these classes therefore play no role.
* The sign `σ = (-1)^ε` is the one for which a multiplier map along `r_p` goes to the principal
  series with the two characters of the block exchanged and their signs kept. With
  `σ = -(-1)^ε` the target would have both signs twisted by `sgn`. In Task 7067's
  `IsBlockFrobData`, these are the fields `sym`, `sign_p` and `sign_q`.
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

This section explains why the propositions are true; none of it is proved in Lean.

**The intertwining integral.** Let `w` be the permutation matrix with `w e_0 = e_2`,
`w e_1 = e_0`, `w e_2 = e_1`, and `n̄(x, y) = 1 + x E_{20} + y E_{21}`. For `f` in the principal
series of `(sgn^{ℓ+1} |·|^a, |·|^b, c)` with `a = t + ℓ/2`, `b = t - ℓ/2`, and
`re (b - s) > 0`, the integral `(I f)(g) = ∫_{ℝ²} f(n̄(x, y) w g) dx dy` converges absolutely.
Two facts give the landing:

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
  `(J_p F)(g) = ± ∫₀^π sin^{δ_p - 2} θ F(r_p(θ) g) dθ`, a left convolution along `r_p`. It
  multiplies `Φ^p_k` by `c_p(k) = ± ∫₀^π sin^{δ_p - 2} θ e^{ikθ} dθ`, with `δ_1 = b - s + 1` and
  `δ_0 = a - s + 1 = δ_1 + ℓ`. Integration by parts gives the recurrence of `IsRecurrent δ_p`,
  and `θ ↦ π - θ` gives `c_p(-k) = (-1)^k c_p(k)`.

Hence, for `re δ > 1`, the statement holds for the multipliers `(c_1, c_0)`.

**All recurrent symmetric multipliers.** For every `δ`, the solutions of `IsRecurrent δ ε`
that are symmetric with sign `(-1)^ε` form a one-dimensional space, also when restricted to a
finite window `|k| ≤ ε + 2M`. By the symmetry it suffices to look at the nonnegative half
`k = ε + 2m ≥ 0`. There the relations `μ(k + 2)(δ + k) = (k + 2 - δ) μ(k)` form a bidiagonal
system. A coefficient `k + 2 - δ` vanishes only if `δ = k + 2 > 0`, and a coefficient `δ + k'`
only if `δ = -k' ≤ 0`, so for a given `δ` only one kind of coefficient vanishes. Then the
system has full rank and its solution space is a line. A polynomial spanning vector is
`P_δ(ε + 2m) = ∏_{r<m} (ε + 2r + 2 - δ) ∏_{m≤r<M} (δ + ε + 2r)`, extended by the symmetry; it
never vanishes on the whole window. For fixed `f`, only finitely many modes enter (`f` is
`O(3)`-finite). The landing condition is then bilinear in the window values of `μ₁` and `μ₀`,
hence polynomial in `δ` for `(P_δ, P'_{δ+ℓ})`. It holds for `re δ > 1`, where `c_p(ε) ≠ 0`
makes `P` a multiple of `c_p` on the window. So it holds identically, and then for every
symmetric recurrent pair at every `δ`.

**Decoupling.** For a given `δ`, replace the exponent `s` of `c` by `t - ℓ/2 - δ + 1`, keeping
its parity, and replace `f` by the `O(3)`-finite function of the new standard module that agrees
with `f` on `O(3)` (extension from `O(3)` by the Iwasawa decomposition; the Library module
`PrincipalSeriesExtension`, and the extension of mode vanishing from `O(n)` to `GL_n` in Task
7067's `RealBlockPositionData`). Nothing in hypotheses 5 and 6 or the conclusion changes.

**The second statement** is the image of the first under `g ↦ J (gᵀ)⁻¹ J` with `J` the
antidiagonal permutation matrix. On `O(3)` this is `k ↦ J k J`, and `J r_0(θ) J = r_1(-θ)`. It
can also be proved directly with `w⁻¹` in place of `w`; the convergence region is then
`re (s - t - ℓ/2) > 0`.

## Use

In the proof of `RealCharacterInducedFiltrationStatement` (and of its mirror
`RealInducedCharacterFiltrationStatement`), the two standard modules of `[d, c]` and `[c, d]`
must be connected by intertwiners. The multiplier maps along one block are not enough. The
composite of a map along `r_1` and then along `r_0`, or along `r_0` and then along `r_1`, lands
in the other standard module exactly by these statements. Used with degenerate (tail)
multipliers, an uncertainty principle on `O(3)`
(`RealOrthogonalBlockUncertaintyStatement`, staged separately) and a count of `O(3)`-types,
this gives the surjections at the integral points where the standard module is irreducible.

## Provenance

Internal and derived. No literature source is claimed and none is formalized. The argument in
"Why the statements hold" is the classical factorization of the long intertwining integral of
the principal series into rank-one integrals, specialized to `GL_3(ℝ)` and to block Fourier
coefficients. The statements were designed for the `GL_3(ℝ)` argument above.
