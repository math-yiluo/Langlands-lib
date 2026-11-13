# The L-factor facts behind the existence of the essential vector

Author: Worker 5032. This module defines one proposition,
`Langlands.Conductor.SphericalLFactorGenerationStatement` (universes `uF`, `uV`).
It is a statement only: nothing here proves it.

## Statement

The binders are exactly those of the published
`Langlands.Conductor.EssentialVectorExistence`
([`EssentialConductorReduction`](EssentialConductorReduction.md)) and of the
published `EssentialVectorStatement`, in the same order:

- a nonarchimedean local field `F : Type uF` of any characteristic, `n : ℕ`, and
  the measurable and Borel structures on `GL_(n+1)(F)`, its upper unipotent
  subgroup, the quotients `LeftUnipotentQuotient n F` and
  `LeftUnipotentQuotient 0 F`, and `GL_1(F)`;
- `q`, `ψ`, `abv`, `ϖ`, `μ` and `h : IsJacquetNormalization q ψ abv ϖ μ`
  (Jacquet's normalizations, documented in [`Essential`](Essential.md));
- `V : Type uV` and `π : Representation ℂ (GeneralLinear ((n + 1) + 1) F) V`
  with `IsGeneric ψ (n + 1) π`;
- `ℓ : glFunctionals ψ (n + 1) π` with `ℓ.val ≠ 0`.

No additive measure on `F` occurs. Write `W_x` for
`inverseSphericalWhittaker h.conductor.1 h.uniformizer q x`, Jacquet's
`W(g; x; ψ̄)` on `GL_(n+1)(F)`, and `Ψ(s, w, W_x)` for the published
`corankOneIntegral ψ abv μ w W_x s`. Write `X = q^(-s)` for
`spectralPoint q s` and `Q_x = ∏ i, P.comp (C (x i) * X)`, the polynomial
`∏_i P(x_i X)`.

The conclusion: there is `P : ℂ[X]` with
`IsCharacterLPolynomial q ψ abv (rankOneQuotientHaar F) 1 π P`, that is
`L(s, π × 1) = P(q^(-s))⁻¹` with `P(0) = 1`, such that the following hold.

1. **Convergence.** For every vector `w` of `coefficientModel π ℓ` and every
   `x : Fin (n + 1) → ℂˣ` there is `a : ℝ` with
   `CorankOneConverges ψ abv μ w W_x s` for every `s` with `a < Re s`.
2. **Laurent numerator.** For every `w` and every `x` there are `a : ℝ`,
   `N : ℤ` and `Q : ℂ[X]` with
   `Ψ(s, w, W_x) · Q_x(q^(-s)) = q^(-Ns) Q(q^(-s))` for every `s` with
   `a < Re s`.
3. **Generation (Jacquet's Lemma 4).** For every `x` there are `k : ℕ`, vectors
   `W : Fin k → coefficientModel π ℓ`, integers `e : Fin k → ℤ` and `a : ℝ` with

   `(∑_j q^(-e_j s) Ψ(s, W_j, W_x)) · Q_x(q^(-s)) = 1`

   for every `s` with `a < Re s`.

`P` is chosen before `w` and `x`. The family `W_j`, `e_j` may depend on `x`.
The three clauses are exactly the hypotheses `hP`, `hconv`, `hpoly` and `hgen`
of the published theorem `exists_isEssentialVector_of_jpss`
([`EssentialExistenceReduction`](EssentialExistenceReduction.md)), for the
model of the given `ℓ`.

Clause 3 is the product form of Jacquet's identity
`∑_j q^(-n_j s) Ψ(s, W_j, W_x) = ∏_i P(x_i q^(-s))⁻¹`. The two forms are
equivalent at each `s`: the product form forces `Q_x(q^(-s)) ≠ 0`, and
conversely the inverse in Jacquet's form is taken where the product is nonzero.
The product form avoids division in Lean.

## Source correspondence

H. Jacquet, *A correction to Conducteur des représentations du groupe
linéaire*, Pacific J. Math. 260 (2012), 515–525, registered
`jacquet-2012-conductor-correction`, file
`/home/taskhub/central-library/Jacquet--A correction to Conducteur des representations du groupe lineaire--2012.pdf`
(printed page 513 + k is PDF page k). Section 1, "Review of the properties of
the L-factor", printed pages 517–519, collects what the existence proof of his
Theorem 1 uses:

- Printed page 516: `I(t_1, ..., t_r)` is the representation induced
  (normalized) from the upper triangular Borel subgroup by the character
  `a ↦ |a_1|^(t_1) ⋯ |a_r|^(t_r)`, with `x_i = q^(-t_i)`.
- Printed page 517: `π` is irreducible admissible generic on `G_r(F)`, its
  Whittaker model is `W(π; ψ)`, and Jacquet's polynomial, written `P_GJ`
  here, is defined by the Godement–Jacquet factor:
  `L_GJ(s, π) = P_GJ(q^(-s))⁻¹`. Here `r = n + 2`. The Lean `P` is a
  different object, the JPSS polynomial; see the subsection below.
- Printed page 519, first paragraph: for `W` in `W(π; ψ)` and `W'` in the
  Whittaker model of the principal series `I(t_1, ..., t_(r-1))`, the integral
  `Ψ(s, W, W') = ∫_(N_(r-1) \ G_(r-1)) W(diag(g, 1)) W'(g) |det g|^(s-1/2) dg`
  "converges absolutely if Re(s) ≫ 0". With `W' = W(x; ψ̄)` this is clause 1.
- Printed page 518, Lemmas 1 and 2: for `Re t_1 ≥ ... ≥ Re t_(r-1)` the
  spherical vector of `I(t)` is cyclic, and its Whittaker function is a nonzero
  multiple of `W(x_1, ..., x_(r-1); ψ̄)` with `x_i = q^(-t_i)`.
- Printed page 519, Lemma 3 (recalled from Jacquet, Piatetski-Shapiro and
  Shalika 1983): finitely many `Ψ(s, W_j, W'_j)` sum to
  `∏_i L_GJ(s + t_i, π)`. By cyclicity of the spherical vector, Jacquet
  rewrites this as
  `∑_j q^(-n_j s) Ψ(s, W_j, W(x; ψ̄)) = ∏_i L_GJ(s + t_i, π)`. Since
  `W(x; ψ̄)` is symmetric in the `x_i`, the ordering assumption is dropped:
  **Lemma 4**, for every tuple of nonzero `x`, there are `W_j` and integers
  `n_j` with `∑_j q^(-n_j s) Ψ(s, W_j, W(x; ψ̄)) = ∏_i P_GJ(q^(-s) x_i)⁻¹`.

Clause 3 has the shape of Lemma 4 with `e_j = n_j`, multiplied through by the
product, on a right half-plane where all integrals converge. It differs in the
polynomial: it uses the JPSS `P`, not `P_GJ`. The subsection below derives
clause 3 for the JPSS `P` directly from JPSS 1983.

Clause 2 is stated by Jacquet only implicitly: on printed pages 520–521 he
multiplies the formal Laurent series of `Ψ(s, W, W(x; ψ̄))` by
`∏ P(X X_i)` and uses that the product is a polynomial in `X, X⁻¹`. It is a
consequence of H. Jacquet, I. I. Piatetski-Shapiro and J. Shalika,
*Rankin–Selberg convolutions*, Amer. J. Math. 105 (1983), 367–464, registered
`jpss-1983-rankin-selberg` (PDF page = printed page − 365):
Theorem (2.7)(ii), printed page 391, gives
`Ψ(s, W, W') ∈ L(s, π × I(x)) ℂ[q^(-s), q^s]`, and Theorem (3.1)(ii), printed
page 405, gives `L(s, π × I(x)) ∈ ∏_i L(s, π × χ_i) ℂ[q^(-s), q^s]` for the
unramified characters `χ_i` with `χ_i(ϖ) = x_i`. Theorem (2.7)(i), printed
page 390, is the convergence of clause 1.

Theorem (3.1)(ii) gives only this divisibility. It supports clause 2, not
clause 3.

### The L-factor, and clause 3 with JPSS factors

Jacquet defines `P_GJ` by the Godement–Jacquet factor. The Lean statement
takes `P` instead from the JPSS 1983 factor of the pair `π × 1` against the
trivial character of `GL_1`: `IsCharacterLPolynomial … 1 π P`, the normalized
generator of the ideal `characterZetaValues` of the rank-one zeta integrals
(JPSS 1983, Theorem (2.7)(ii)). The published `EssentialVectorStatement` and
`IsEssentialVector` use the same `P`. The statement does not assert any
comparison of `P` with `P_GJ`, and the derivation below does not use one.
Twisting alone cannot replace such a comparison: it relates JPSS factors only
to other JPSS factors. What the derivation needs is the equality of the JPSS
pair factor `L(s, π × I(t))` with the product of the rank-one JPSS factors,
which comes from the following results of JPSS 1983 (`L` below is always the
JPSS factor):

- Remark (3.3), printed page 405: `L(s, π × σ)` depends only on the Whittaker
  model of `π`.
- (8.4) Proposition, printed pages 451–452: if `π` and `σ` are tempered,
  induced from square-integrable `π_i` and `σ_j`, then
  `L(s, π × σ) = ∏_(i,j) L(s, π_i × σ_j)`. Such induced representations are
  irreducible (stated in (8.4)).
- (9.4) Proposition, printed page 458, equation (3) (proof on pages 458–462):
  if `ξ = Ind(π_(i,0) ⊗ α^(u_i))` and `η = Ind(σ_(j,0) ⊗ α^(v_j))` are of
  Langlands' type (tempered `π_(i,0)` and `σ_(j,0)`, `u_1 > ... > u_m`,
  `v_1 > ... > v_n`), then `L(s, ξ × η) = ∏_(i,j) L(s, π_i × σ_j)`. By the
  paragraph containing equation (4), a generic irreducible `π` has the same
  Whittaker model as its standard module `ξ`, so `L(s, π × η) = L(s, ξ × η)`.

Let `Re t_1 ≥ ... ≥ Re t_(r-1)` and let `χ_l = |·|^(t_l)`, so that
`χ_l(ϖ) = x_l = q^(-t_l)`; by Jacquet's page 516, `I(t)` is induced from the
upper Borel subgroup by `χ_1, ..., χ_(r-1)` in this order. Group the `χ_l`
with equal real part into blocks
`σ_(j,0) ⊗ α^(v_j)`, where `σ_(j,0)` is a unitary unramified principal series
(tempered) and `v_1 > ... > v_n`. By induction in stages `I(t)` is then of
Langlands' type. Equation (9.4)(3) gives
`L(s, π × I(t)) = ∏_(i,j) L(s, π_i × σ_j)`. Within each block, (8.4), after the
shift `s ↦ s + u_i + v_j`, gives
`L(s, π_i × σ_j) = ∏_(l in block j) L(s, π_i × χ_l)`. Equation (9.4)(3) with
`η = χ_l` (a character of `GL_1` is quasi-tempered) gives
`∏_i L(s, π_i × χ_l) = L(s, π × χ_l)`. Hence

`L(s, π × I(t)) = ∏_l L(s, π × χ_l)`.

Twisting by the unramified `χ_l` shifts `s` by `t_l` in every rank-one zeta
integral. So the ideal for `χ_l` is the ideal for `1`, shifted, and
`L(s, π × χ_l) = P(x_l q^(-s))⁻¹`. By Theorem (2.7)(ii) for the pair
`(π, I(t))`, the span of the integrals `Ψ(s, W, W')` is the fractional ideal
generated by `L(s, π × I(t))`. So finitely many `Ψ(s, W_j, W'_j)` sum to
`∏_l P(x_l q^(-s))⁻¹`. This is the analogue of Jacquet's Lemma 3 with JPSS
factors, derived from the product equality above, not from identifying the two
theories by twisting. Jacquet's cyclicity argument (Lemmas 1 and 2) and the
symmetry of `W(x; ψ̄)` in `x` then give the analogue of Lemma 4 for the JPSS
`P`, which is clause 3, exactly as on his page 519.

## Relation to other statements

The published `SphericalLaurentFunctionalEquationStatement`
([`SphericalLaurentFunctionalEquationStatement`](SphericalLaurentFunctionalEquationStatement.md))
also contains clause 1 and a Laurent-numerator form of clause 2, but it takes
`P` and an epsilon factor `(c, m)` as hypotheses, relative to an additive
measure `ν` with `IsSelfDual ψ ν`. `EssentialVectorExistence` has no such `ν`,
and the existence of a self-dual measure is not available in the Library over
an arbitrary nonarchimedean local field. The present statement therefore
asserts the existence of `P` itself and needs no `ν`. It also contains
clause 3, which no published statement asserts.

## Use

Applied to the given data, the statement supplies the hypotheses `P`, `hP`,
`hconv`, `hpoly` and `hgen` of the published `exists_isEssentialVector_of_jpss`.
That theorem then gives the published `EssentialVectorExistence`. Together with
the four other inputs of the published `essentialConductorStatement_of`, this
gives the target `EssentialConductorStatement` of Task 5032.

## What it does not assert

It does not identify `∏_i P(x_i X)⁻¹` with the L-factor of `π × I(x)`, does not
assert a functional equation, an epsilon factor or a dual L-polynomial, and
does not assert meromorphic continuation beyond the Laurent form of clause 2.
It does not assert uniformity in `x` of the half-planes or of `N`. It says
nothing about integrals against Whittaker functions other than `W_x`.

## Imports

Only the published `Langlands.Representation.Conductor.EssentialStatement`,
whose import closure supplies all names used, including
`IsCharacterLPolynomial`, `rankOneQuotientHaar`, `CorankOneConverges`,
`corankOneIntegral`, `inverseSphericalWhittaker` and `spectralPoint`.
`Polynomial` is opened for `ℂ[X]`, `C` and `X`.
