# The mirror of the landing statements on `GL_3(ℝ)`

Module `Langlands.Representation.Archimedean.RealSwapLandingMirror` (namespace
`Langlands.Archimedean.RealSwapLandingMirror`).

## Role and provenance

This module is an internal step of the Task 7134 proof of
`RealInducedCharacterFiltrationStatement` (see `RealInducedCharacterFiltration.md`). It
belongs to the proof of the landing statements of `RealSwapLandingStatement` (statement
module of Worker 763, Task 7133, statement candidate `a11b2199`). Worker 763 proves
`RealSwapLandingInducedFirstStatement`. This module derives
`RealSwapLandingCharacterFirstStatement` from it by a symmetry of `GL_3(ℝ)`. The main
theorem takes the induced-first statement as a hypothesis and does not prove it. No
literature statement is formalized; the symmetry argument is internal to this development.

Notation: `c : RealCharacterData` has parity `ε₁`; `d : ComplexCharacterData` has weight
`m`; `ℓ = |m|`. `r_0(θ) = blockRotation 3 0 θ` rotates the coordinates `0, 1`, and
`r_1(θ) = blockRotation 3 1 θ` rotates the coordinates `1, 2`.
`Φ^p_j F = blockFourierCoefficient 3 p j F`, so
`Φ^p_j F (g) = ∫_0^{2π} F(r_p(θ) g) e^{-ijθ} dθ`. `O(3)` is `unitaryCompact ℝ 3`.

## The mirror matrix

`mirrorMatrix` is `κ₀ = !![0, 0, 1; 0, -1, 0; 1, 0, 0] = diag(1, -1, 1) · J`, where `J` is
the antidiagonal permutation matrix. `mirror` and `mirrorUnit` are `κ₀` as an element of
`O(3)` and of `GL_3(ℝ)`. The proved facts are the following.

* `mirrorMatrix_mem`: `κ₀` is orthogonal.
* `mirror_mul_mirror`, `mirrorUnit_mul_mirrorUnit_mul`: `κ₀² = 1`, so
  `κ₀ (κ₀ x) = x`.
* `mirror_mul_blockRotation_zero`, `mirror_mul_blockRotation_one`:
  `κ₀ r_0(θ) = r_1(θ) κ₀` and `κ₀ r_1(θ) = r_0(θ) κ₀`, with the same angle `θ`. The sign
  `-1` in the middle entry makes the angle the same; without it, the angle would change
  sign.
* `mirror_mul_signDiagonal`: `κ₀ · diag(sgn a₀, sgn a₁, sgn a₂) =
  diag(sgn a₂, sgn a₁, sgn a₀) · κ₀`.

All of them are checked entrywise (`fin_cases`).

## Auxiliary lemmas

* `isRecurrent_congr`, `isSymmetric_congr`: the recurrence `IsRecurrent δ ε μ` and the
  symmetry `IsSymmetric ε σ μ` of `RealBlockMultiplier` depend on `ε` only through its
  parity. (The symmetry lemma also allows a provably equal sign `σ = σ'`.)
* `neg_one_pow_congr`, `even_sub_mod`, `even_sub_mod'`, `pow_mod_two`: parity
  arithmetic.
* `sq_signReal`, `character_signUnit`, `realInducedFirstCharacter_signUnit`,
  `realInducedSecondCharacter_signUnit`: the values of the position characters at signs.
  A real character `c` gives `sgn(x)^{ε₁}`. The two position characters of the
  induction block `d` give `sgn(x)^{ℓ+1}` and `1`.
* `sgnDet_signDiagonal`: `sgnDet(diag(sgn a)) = ∏ᵢ sgn aᵢ`; `sgnDet_ne_zero`.
* `sign_identity`: if `s₁² = s₂² = 1`, then
  `s₂^{ε₁} s₁^{ℓ+1} · 1 · (s₂ s₁ s₀)^{ℓ+1} = s₀^{ℓ+1} · 1 · s₂^{(ℓ+1+ε₁) mod 2}`.
  The proof is `ring` together with `pow_mod_two`.

## The mirror of a function

* `blockFourierCoefficient_comp_mirror`: assume `κ₀ r_p(θ) = r_q(θ) κ₀` for all `θ`. Then
  `Φ^p_j (Ψ(κ₀ ·))(g) = Φ^q_j Ψ (κ₀ g)`. The integrands agree pointwise.
* `mirrorFun e φ` is the function `x ↦ φ(κ₀ x) · sgnDet(κ₀ x)^e`.
  `continuous_mirrorFun` shows that it is continuous when `φ` is.
* `blockFourierCoefficient_mirrorFun`: under the same hypothesis on `p, q`,
  `Φ^p_j (mirrorFun e φ)(g) = sgnDet(κ₀ g)^e · Φ^q_j φ (κ₀ g)`. This combines the previous
  lemma with `blockFourierCoefficient_mul_sgnDet_pow` (module `RealSwapFLanding`).

## The mirror of the standard module of `[c, d]`

* `mirrorCharacter c d` is the real character data `c'` of parity `(ℓ + 1 + ε₁) mod 2` and
  exponent `0` (`RealJacquetFrobenius.charData`). Its parity is recorded in
  `mirrorCharacter_parity`.
* `mirrorExt c d f` takes the function `x ↦ f(x) sgnDet(x)^{ℓ+1}` on `O(3)` and transports
  it by `κ₀` (`RealKTypeTransport.transport`: `κ ↦ F(κ₀ κ)`). It then extends the result
  to `GL_3(ℝ)` as a principal series function with the exponents of `[d, c']`, using the
  Library's `PrincipalSeriesExtension.extension`.
* `mirrorExt_eq`: on `O(3)`, `mirrorExt c d f = mirrorFun (ℓ+1) f`. This follows from
  `extension_unitary` and `transport_apply`.
* `transport_mirror_signDiagonal`: let `f` lie in the principal series of the position
  characters of `[c, d]`. Then the transported function is equivariant under sign matrices
  for the position characters of `[d, c']`:
  `F(diag(sgn a) κ) = χ_{[d,c']}(sgn a) F(κ)`. The proof moves `diag(sgn a)` past `κ₀`
  (`mirror_mul_signDiagonal`), which reverses `a`. It then uses the equivariance of `f`
  (`PartialJacquet.signDiagonal_toUnits`) and the multiplicativity of `sgnDet`. The
  resulting identity of characters is `sign_identity`, with `s_i = sgn aᵢ`, after
  `JacquetKernel.principalSeriesCharacter_sign` and the sign values above. This is where
  the twist `sgnDet^{ℓ+1}` and the parity `(ℓ+1+ε₁) mod 2` of `c'` are needed.
* `mirrorExt_mem`: let `f` be an `O(3)`-finite function of the standard module of
  `[c, d]`. Then `mirrorExt c d f` is an `O(3)`-finite function of the standard module of
  `[d, c']`.
  - It is an `O(3)`-finite principal series function. This follows from
    `extension_mem_kFiniteFunctions`, with continuity from `continuous_transport` and
    finite-dimensionality from `finiteDimensional_transport` and
    `mem_kFiniteVectors_mul_sgnDet_pow`. The sign equivariance is
    `transport_mirror_signDiagonal`.
  - For the block conditions it suffices to check them on `O(3)`
    (`RealKTypeTransport.mem_realStandardModule_of_unitaryCompact`). The only induction
    block of `[d, c']` is at position `0`. For `|j| < ℓ` and `x ∈ O(3)`,
    `Φ⁰_j (mirrorExt c d f)(x) = sgnDet(κ₀ x)^{ℓ+1} Φ¹_j f(κ₀ x) = 0`. The first equality
    uses `blockFourierCoefficient_congr`, `mirrorExt_eq` and
    `blockFourierCoefficient_mirrorFun` with `κ₀ r_0 = r_1 κ₀`. The second holds because
    the induction block of `[c, d]` sits at position `1`.

## Main theorem

`characterFirst_of_inducedFirst (hI : RealSwapLandingInducedFirstStatement) :
RealSwapLandingCharacterFirstStatement`.

### Proof

Take the data of the character-first statement: `c`, `d`, `δ`, the multipliers `μ₀` (for
`δ` on the class `ℓ + 1 + ε₁`) and `μ₁` (for `δ + ℓ` on the class `ε₁`), and `f, h, u` with
`Φ⁰_k h = μ₀ k Φ⁰_k f` and `Φ¹_k u = μ₁ k Φ¹_k h` on `O(3)`. Put `e = ℓ + 1` and apply `hI`
to the following data:

* the real character `c'` and the same `d` and `δ`;
* `μ₀` as the multiplier along `r_1`, and `μ₁` as the multiplier along `r_0`;
* the functions `mirrorExt c d f`, `mirrorFun e h` and `mirrorFun e u`.

The hypotheses of `hI` are checked as follows.

1. Recurrences and symmetries. `hI` asks for the multiplier along `r_1` on the class
   `(ε₁' : ℤ)` with sign `(-1)^{ε₁'}`, where `ε₁' = (ℓ + 1 + ε₁) mod 2` is the parity of
   `c'`. It asks for the multiplier along `r_0` on the class `ℓ + 1 + ε₁'` with sign
   `(-1)^{ℓ+1+ε₁'}`. The first class has the parity of `ℓ + 1 + ε₁` and the second the
   parity of `ε₁`. So the hypotheses on `μ₀` and `μ₁` transfer by `isRecurrent_congr`
   and `isSymmetric_congr`.
2. Membership: `mirrorExt_mem`. Continuity: `continuous_mirrorFun`.
3. Multiplier relations at `x ∈ O(3)`. By `blockFourierCoefficient_mirrorFun`,
   `Φ¹_k` of a mirror at `x` is `sgnDet(κ₀ x)^e Φ⁰_k` of the original at `κ₀ x`, and
   `Φ⁰_k` of a mirror is `sgnDet(κ₀ x)^e Φ¹_k` of the original. On `O(3)`,
   `mirrorExt c d f` agrees with `mirrorFun e f` (`blockFourierCoefficient_congr`,
   `mirrorExt_eq`). Since `κ₀ x ∈ O(3)`, the relations for `h` and `u` at `κ₀ x` give
   `Φ¹_k (mirrorFun e h) = μ₀ k Φ¹_k (mirrorExt c d f)` and
   `Φ⁰_k (mirrorFun e u) = μ₁ k Φ⁰_k (mirrorFun e h)` at `x`.

So `hI` gives `Φ¹_k (mirrorFun e u) = 0` on `O(3)` for `|k| < ℓ`. Let `g ∈ O(3)` and
`|k| < ℓ`, and evaluate at `κ₀ g ∈ O(3)`. Since `κ₀ (κ₀ g) = g`, this gives
`sgnDet(g)^e · Φ⁰_k u (g) = 0`. As `sgnDet(g) ≠ 0`, `Φ⁰_k u (g) = 0`, which is the
conclusion of the character-first statement.
