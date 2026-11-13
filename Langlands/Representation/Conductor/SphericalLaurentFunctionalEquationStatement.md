# The corank-one functional equation against spherical Whittaker functions, all parameters

Author: Worker 5077. This module defines one proposition,
`Langlands.Conductor.SphericalLaurentFunctionalEquationStatement` (universes
`uF`, `uV`). It is a statement only: nothing here proves it.

## Statement

The binders up to and including the epsilon factor are those of the published
`Langlands.Conductor.ConductorMinimalityStatement`
([`ConductorMinimalityStatement`](ConductorMinimalityStatement.md)), in the same
order:

- a nonarchimedean local field `F : Type uF` of any characteristic, with
  `T2Space`, `TotallyDisconnectedSpace` and a Borel measurable structure, and
  `n : ℕ` with the measurable and Borel structures of that statement;
- `q`, `ψ`, `abv`, `ϖ`, `μ` and `h : IsJacquetNormalization q ψ abv ϖ μ`
  (Jacquet's normalizations, documented in [`Essential`](Essential.md)), and an
  additive Haar measure `ν` with `IsSelfDual ψ ν`;
- `V : Type uV`, `π : Representation ℂ (GeneralLinear ((n + 1) + 1) F) V` with
  `IsGeneric ψ (n + 1) π`, and `ℓ : glFunctionals ψ (n + 1) π` with `ℓ.val ≠ 0`;
- `P : ℂ[X]` with `IsCharacterLPolynomial q ψ abv (rankOneQuotientHaar F) 1 π P`,
  that is `L(s, π × 1) = P(q^(-s))⁻¹`;
- `c : ℂˣ`, `m : ℤ` with
  `IsPairEpsilonFactor q ψ abv ν π (rankOneCharacter 1) (c, m)`, that is
  `ε(s, π × 1, ψ) = c q^(-ms)`.

The conclusion: there is `Pdual : ℂ[X]` with `Pdual.coeff 0 = 1` such that for
every vector `v` of `coefficientModel π ℓ` and every `x : Fin (n + 1) → ℂˣ`,
writing `W_x = inverseSphericalWhittaker h.conductor.1 h.uniformizer q x` (the
function `W(g; x; ψ̄)` on `GL_(n+1)(F)`):

1. the corank-one integral `corankOneIntegral ψ abv μ v.val W_x s` converges
   absolutely (`CorankOneConverges`) for all `s` in some right half-plane;
2. the dual integral `corankOneIntegral (ψ.scale (-1)) abv μ ṽ W̃_x s` converges
   absolutely for all `s` in some right half-plane, where
   `ṽ = firstDualFunction ψ (n + 1) v.val` is `g ↦ v(w₀ ᵗg⁻¹)` and
   `W̃_x = secondDualFunction ψ n W_x` is `g ↦ W_x(w₀ ᵗg⁻¹)`;
3. there are a Laurent polynomial `Q` and a rational function `Rdual` such that
   the first integral has the rational continuation
   `laurentToRatFunc Q * essentialFactor P x`, that is `Q(X) ∏ i, P(x_i X)⁻¹`
   in `X = q^(-s)`, the second has the rational continuation `Rdual`, and
   `NormalizedFunctionalEquation q (∏ i, P(x_i X)) (∏ i, Pdual(x_i⁻¹ X)) 1
   (c^(n+1) (∏ i, x_i)^m) (n + 1) ((n + 1) m) (Q ∏ P(x_i X)⁻¹) Rdual` holds: at
   every `s` where both continuations are defined,

   `∏ Pdual(x_i⁻¹ q^(-(1-s))) Rdual(q^(-(1-s)))
     = c^(n+1) (∏ x_i)^m q^(-(n+1)ms) ∏ P(x_i q^(-s)) R(q^(-s))`

   with `R = Q ∏ P(x_i X)⁻¹`.

`Pdual` is chosen before `v` and `x`. The scalar `ζ` of
`NormalizedFunctionalEquation` is `1`, and the exponent `e = n + 1` is then
irrelevant.

## Relation to the published unitary statement

The published `Langlands.Conductor.SphericalCorankOneFunctionalEquationStatement`
([`SphericalCorankOneFunctionalEquationStatement`](SphericalCorankOneFunctionalEquationStatement.md),
proof task `685d39c3-c280-41e2-bdd5-6012dd1d2339`) states the same identity of
JPSS 1981, (4.2)(3), with different hypotheses and conclusions. It takes both
L-polynomials, of `π` and of its inverse-transpose pullback, as hypotheses,
restricts to unitary parameters `|x_i| = 1`, and gives arbitrary rational
continuations. The present statement takes only `P` and `(c, m)` as hypotheses.
It covers every `x`, asserts existence of the dual polynomial, and records that
the numerator `Q` of the forward continuation is a Laurent polynomial. These
three features are what the end of the proof of JPSS 1981, Theorem (5.1),
printed pages 213–214, uses for a `K(u)`-fixed vector: no dual L-polynomial is
available there, the scaled identity is asserted for every `x`, and the exponent
comparison needs the Laurent-polynomial numerator. Neither statement implies the
other as stated; both follow from JPSS 1983, Theorems (2.7) and (3.1).

## Source correspondence

H. Jacquet, I. I. Piatetski-Shapiro and J. Shalika, *Conducteur des
représentations du groupe linéaire*, Math. Ann. 256 (1981), 199–214, registered
`jpss-1981-conductor`, file
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Conducteur des representations du groupe lineaire--1981.pdf`
(printed page 199 is PDF page 1). Section (4.2), printed pages 208–209,
identity (3): for `|x_i| = 1` the induced representation `I(x_1, ..., x_(r-1))`
of `G_(r-1)` is irreducible and generic, `W' = W(x; ψ̄)` lies in its Whittaker
model, `W̃' = W(x⁻¹; ψ)`, and "les résultats énoncés dans [J-P-S2] montrent que

`Ψ(q⁻¹X⁻¹, W̃, W̃') ∏ P_π̃(q⁻¹X⁻¹X_i⁻¹) = ∏ ε_π(X X_i, ψ) Ψ(X, W, W') ∏ P_π(X X_i)`"

for every `W'` in that model. Taking `W' = W(x; ψ̄)` gives the specialization
of (4.2)(1); (4.2)(7) on printed page 210 is the same identity for the
spherical transform. In the Lean statement:

- `r = n + 2`; `Ψ(X, W, W')` with `X = q^(-s)` is `corankOneIntegral` at `s`,
  and `Ψ(q⁻¹X⁻¹, W̃, W̃')` is the dual integral at `1 - s`
  (`spectralPoint q (1 - s) = q⁻¹ (q^(-s))⁻¹`);
- `P_π` is `P`; `P_π̃` is the existentially quantified `Pdual`, normalized by
  `Pdual.coeff 0 = 1`. The contragredient `π̃` is realized, as in JPSS 1983,
  Section (2.1), printed page 386, by the inverse-transpose pullback with the
  character `ψ̄`; the statement does not identify `Pdual` with an
  `IsCharacterLPolynomial` of that pullback;
- `ε_π(X X_i, ψ) = c (x_i X)^m`: the epsilon factor of `π ⊗ χ_i` for the
  unramified character `χ_i` with `χ_i(ϖ) = x_i` is `ε(s + t_i, π, ψ)` with
  `x_i = q^(-t_i)`, and its product over `i` is the monomial
  `epsilonMonomial q (c^(n+1) (∏ x_i)^m) ((n+1) m)`;
- the dual integral is the published `dualUnequalRankModelIntegralAt` with
  blocks `j = k = 0` and second functional the dual of the test, since the block
  Weyl element `blockWeylAt n (n + 1) = diag(I_(n+1), w_1)` is the identity.

The statement goes beyond the displayed identity in three ways, each a part of
the theory of H. Jacquet, I. I. Piatetski-Shapiro and J. Shalika,
*Rankin–Selberg convolutions*, Amer. J. Math. 105 (1983), 367–464 (registered
`jpss-1983-rankin-selberg`, PDF page = printed page − 365), that the 1981
argument uses:

- **All `x`, not only `|x_i| = 1`.** Theorem (2.7), printed pages 390–391,
  holds for representations of Whittaker type, and Theorem (3.1), printed pages
  404–405, for representations induced from representations of Whittaker
  type. H. Jacquet, *A correction to Conducteur des représentations du groupe
  linéaire*, Pacific J. Math. 260 (2012), 515–525 (registered
  `jacquet-2012-conductor-correction`), §1, printed pages 517–519, Lemmas 1–2:
  for `Re t_1 ≥ ... ≥ Re t_(r-1)` the spherical vector of `I(t)` is cyclic and
  its Whittaker function is a nonzero multiple of `W(x; ψ)`, `x_i = q^(-t_i)`;
  the explicit function is symmetric in `x`. Jacquet uses the identity for all
  `x` (printed page 521, the display before "The factors are monomials").
- **Absolute convergence** on right half-planes: JPSS 1983, Theorem (2.7)(i).
- **The Laurent-polynomial numerator** `Q`: JPSS 1983, Theorem (2.7)(ii)
  (printed page 391), gives `Ψ(s, W, W') ∈ L(s, π × I(x)) ℂ[q^(-s), q^s]`, and
  Theorem (3.1)(ii) (printed page 405) gives
  `L(s, π × I(x)) ∈ ∏ L(s, π ⊗ χ_i) ℂ[q^(-s), q^s]` with
  `L(s, π ⊗ χ_i) = P(x_i q^(-s))⁻¹`. JPSS 1981 (4.2), printed page 209 ("chaque
  membre est un polynôme en X, X⁻¹") and Jacquet 2012, printed page 521, read
  the functional equation as an identity of formal Laurent series to obtain
  this property; an identity of rational functions alone does not give it, so
  the statement records it explicitly.

The sign: in JPSS 1983, Theorem (2.7)(iii), display (2), printed page 391, the
functional equation carries `ω_(π')(-1)^(r-1)` for the central character of the
smaller-rank representation `π'`. For the unramified `π' = I(x)` this is `1`;
correspondingly `W_x(-g) = W_x(g)` because `-1 ∈ GL_(n+1)(O)`. Hence `ζ = 1`.

## Use

The reduction module `ConductorMinimalityReduction`, a separate candidate of
Task 5549, derives the published `ConductorMinimalityStatement` from this
statement and `Langlands.Whittaker.MirabolicRestrictionInjectivityStatement`,
following JPSS 1981, printed pages 213–214.

## What it does not assert

It does not identify `Pdual` with an L-polynomial of the inverse-transpose
pullback, does not assert that `∏ P(x_i X)⁻¹` is the L-factor of `π × I(x)`, and
does not assert existence of `P` or of `(c, m)`, which are hypotheses. It says
nothing about integrals against other vectors of the principal series.

## Imports

Only the published `Langlands.Representation.Conductor.EssentialStatement`,
whose import closure supplies all names used, including `firstDualFunction`,
`secondDualFunction`, `NormalizedFunctionalEquation`, `laurentToRatFunc` and
`essentialFactor`. `Polynomial` is opened for `ℂ[X]`, `C` and `X`.
