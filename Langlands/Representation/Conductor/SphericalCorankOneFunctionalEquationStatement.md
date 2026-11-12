# The corank-one functional equation against unitary spherical functions

Author: Worker 5008. This module defines one proposition,
`Langlands.Conductor.SphericalCorankOneFunctionalEquationStatement`
(universes `uF`, `uV`). It is a statement only: nothing here proves it, and no
declaration assumes it.

It is the identity that Jacquet, Piatetski-Shapiro and Shalika (1981) use in
(4.2) and again in (5.3), for an irreducible generic `π` of `GL_r(F)` and the
spherical Whittaker functions of the unramified unitary principal series of
`GL_(r-1)(F)`. It was split out of Task 5548 (the proof of the published
`EssentialDualComparisonStatement`), because the Library has no
Rankin–Selberg functional equation with multiplicativity of gamma factors over
an arbitrary nonarchimedean local field.

## Statement

The binders are those of the published
`Langlands.Conductor.EssentialDualComparisonStatement`
([`EssentialDualComparisonStatement`](EssentialDualComparisonStatement.md)), in
the same order, except that the two essential vectors `w` and `w'` are removed
and two L-polynomials are added:

- a field `F : Type uF` with `Field F`, `ValuativeRel F`, `TopologicalSpace F`,
  `IsNonarchimedeanLocalField F`, `T2Space F`, `TotallyDisconnectedSpace F`
  and a Borel measurable structure; any characteristic is allowed and there is
  no `PadicField` restriction;
- `n : ℕ` with the measurable and Borel structures of that statement on
  `GL_(n+1)(F)`, its unipotent subgroup, `GL_1(F)`, its unipotent subgroup,
  and the quotients `LeftUnipotentQuotient n F` and `LeftUnipotentQuotient 0 F`;
- `q`, `ψ`, `abv`, `ϖ`, `μ`, `h : IsJacquetNormalization q ψ abv ϖ μ` and
  `h' : IsJacquetNormalization q (ψ.scale (-1)) abv ϖ μ` (Jacquet's
  normalizations for `ψ` and for `ψ̄ = ψ.scale (-1)`, documented in
  [`Essential`](Essential.md));
- an additive Haar measure `ν` on `F` with `IsSelfDual ψ ν`.

Then for every `V : Type uV` and
`π : Representation ℂ (GeneralLinear ((n + 1) + 1) F) V` with
`IsGeneric ψ (n + 1) π`:

- every `ℓ : glFunctionals ψ (n + 1) π` with `ℓ.val ≠ 0`;
- every `ℓ' : glFunctionals (ψ.scale (-1)) (n + 1) (inverseTransposePullback π)`
  with `ℓ'.val = (dualFunctional ψ π ℓ).val`;
- every `c : ℂˣ` and `m : ℤ` with
  `IsPairEpsilonFactor q ψ abv ν π (rankOneCharacter 1) (c, m)`;
- every `P Pdual : ℂ[X]` with
  `IsCharacterLPolynomial q ψ abv (rankOneQuotientHaar F) 1 π P` and
  `IsCharacterLPolynomial q (ψ.scale (-1)) abv (rankOneQuotientHaar F) 1
  (inverseTransposePullback π) Pdual`;
- every `v : V` and `x : Fin (n + 1) → ℂˣ` with `‖(x i : ℂ)‖ = 1` for all `i`;

write `W = coefficientMap π ℓ v`, `W̃ = coefficientMap (inverseTransposePullback π) ℓ' v`,
`W' = inverseSphericalWhittaker h.conductor.1 h.uniformizer q x` and
`W̃' = inverseSphericalWhittaker h'.conductor.1 h'.uniformizer q x⁻¹`. Then:

1. there is `a : ℝ` such that `CorankOneConverges ψ abv μ W W' s` for every
   `s : ℂ` with `a < s.re`;
2. there is `a : ℝ` such that
   `CorankOneConverges (ψ.scale (-1)) abv μ W̃ W̃' s` for every `s : ℂ` with
   `a < s.re`;
3. there are `R Rdual : RationalFunctions` with
   `HasRationalContinuation q (corankOneIntegral ψ abv μ W W') R`,
   `HasRationalContinuation q (corankOneIntegral (ψ.scale (-1)) abv μ W̃ W̃') Rdual`
   and

   ```
   NormalizedFunctionalEquation q
     (∏ i, P.comp (C (x i) * X)) (∏ i, Pdual.comp (C (x⁻¹ i) * X))
     1 (c ^ (n + 1) * (∏ i, x i) ^ m) 0 ((n + 1) * m) R Rdual
   ```

By the published definition of `NormalizedFunctionalEquation` (sign exponent
`0`, so the sign `1 ^ 0 = 1` plays no role), the last clause says: for every
`s : ℂ` at which neither `R` (at `q^(-s)`) nor `Rdual` (at `q^(-(1-s))`) has a
pole,

```
∏ᵢ Pdual(xᵢ⁻¹ q^(-(1-s))) · Rdual(q^(-(1-s)))
  = c^(n+1) (∏ᵢ xᵢ)^m q^(-(n+1)ms) · ∏ᵢ P(xᵢ q^(-s)) · R(q^(-s)).
```

The rank of `π` is `r = n + 2 ≥ 2`, and `n = 0` (rank two against `GL_1`) is
included. `HasRationalContinuation` only asserts equality with a rational
function on some right half-plane; the convergence clauses 1 and 2 are stated
separately so that the integrals are genuine absolutely convergent integrals
there.

## Source correspondence

H. Jacquet, I. I. Piatetski-Shapiro and J. Shalika, *Conducteur des
représentations du groupe linéaire*, Math. Ann. 256 (1981), 199–214; registered
source `jpss-1981-conductor` (printed page 199 is PDF page 1). Pages read:

- (4.2), display (1), printed page 208 (PDF page 10): for every `W` in
  `𝒲(π; ψ)`,
  `Ψ(q⁻¹X⁻¹, W̃, X₁⁻¹, ..., X_(r-1)⁻¹) ∏ P_π̃(q⁻¹X⁻¹Xᵢ⁻¹)
    = ∏ ε_π(XXᵢ, ψ) Ψ(X, W, X₁, ..., X_(r-1)) ∏ P_π(XXᵢ)`,
  an identity of Laurent series in `X` with coefficients in the symmetric
  polynomials in the `Xᵢ`. The text says that it suffices to prove it after
  replacing the `Xᵢ` by complex numbers `xᵢ ≠ 0`, and even only when all `xᵢ`
  have modulus one; then `σ = I(x₁, ..., x_(r-1))` is irreducible and generic.
- (4.2), display (3), printed page 209 (PDF page 11): with
  `W' = W(x₁, ..., x_(r-1); ψ̄)` in `𝒲(σ; ψ̄)` and `W(g; x₁⁻¹, ..., x_(r-1)⁻¹; ψ)`
  equal to `(W')~`, "les résultats énoncés dans [J-P-S 2] montrent que"
  `Ψ(q⁻¹X⁻¹, W̃, W̃') ∏ P_π̃(q⁻¹X⁻¹xᵢ⁻¹) = ∏ ε_π(Xxᵢ, ψ) Ψ(X, W, W') ∏ P_π(Xxᵢ)`
  for every `W'`; taking `W' = W(x; ψ̄)` gives the specialization of (1).

The present statement is display (3) for `W' = W(g; x; ψ̄)` and
`W̃' = W(g; x⁻¹; ψ)`, with `|xᵢ| = 1`, written in the variable `X = q^(-s)`, so
that `q⁻¹X⁻¹ = q^(-(1-s))`. The correspondence is:

- `Ψ(X, W, W')` is `corankOneIntegral ψ abv μ W W'` at `s`, through its
  rational continuation `R`; `Ψ(q⁻¹X⁻¹, W̃, W̃')` is
  `corankOneIntegral (ψ.scale (-1)) abv μ W̃ W̃'` at `1 - s`, through `Rdual`.
  The corank-one integral is `∫ W(diag(g, 1)) W'(g) |det g|^(s - 1/2) dg` over
  `N_(r-1) \ GL_(r-1)(F)` with the measure `μ`; the dual integral is the same
  integral for the character `ψ̄`, as in the source where `W̃ ∈ 𝒲(π̃; ψ̄)`.
- `W̃` is the coefficient of the same vector `v` for `ℓ'`. The published
  `dualFunction_coefficient` shows that this is the source's
  `W̃(g) = W(w_r ᵗg⁻¹)` of (1.2)(3), printed page 200, for `W` the coefficient
  of `v` for `ℓ`; the dual model is explained in
  [`EssentialDualComparisonStatement`](EssentialDualComparisonStatement.md).
  Quantifying over `v` is quantifying over every `W` of the model.
- `W(g; x; ψ̄)` is the published `inverseSphericalWhittaker` for `ψ` (the
  spherical function for the inverse standard character), as in the published
  `SatisfiesEssentialIdentity`; `W(g; x⁻¹; ψ)` is the same function for
  `ψ.scale (-1)` at `x⁻¹`, whose inverse standard character is the standard
  character of `ψ`. The identification of `inverseSphericalWhittaker` with
  Jacquet's characterization is discussed in [`EssentialStatement`](EssentialStatement.md).
- `P_π(Xxᵢ)` is `P.comp (C (x i) * X)` evaluated at `q^(-s)`, and
  `P_π̃(q⁻¹X⁻¹xᵢ⁻¹)` is `Pdual.comp (C (x⁻¹ i) * X)` evaluated at
  `q^(-(1-s))`; these are the polynomials of the published `essentialFactor`.
- `ε_π(Xxᵢ, ψ)` with `ε_π(X, ψ) = c X^m` is `c xᵢ^m q^(-ms)`, and the product
  over the `n + 1` indices is `c^(n+1) (∏ xᵢ)^m q^(-(n+1)ms)`, the
  `epsilonMonomial q (c ^ (n + 1) * (∏ i, x i) ^ m) ((n + 1) * m)`.

### Why the identity holds: JPSS 1983

H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika, *Rankin–Selberg
convolutions*, Amer. J. Math. 105 (1983), 367–464; registered source
`jpss-1983-rankin-selberg` (scan with one cover page; PDF page = printed
page − 365). This is the source's `[J-P-S 2]`. Pages read rendered:

- Theorem (2.7), printed pages 390–391 (PDF pages 25–26): for `π` of `G_r` and
  `π'` of `G_t` of Whittaker type, the integrals converge absolutely for
  `Re(s)` large (i), are rational functions of `q^(-s)` and span a fractional
  ideal generated by `L(s, π × π') = P(q^(-s))⁻¹` with `P(0) = 1` (ii), and for
  `t ≤ r - 1`, with `k = r - t - 1 - j`, satisfy the functional equation (2)
  `Ψ(1 - s, ρ(w_(r,t)) W̃, W̃'; k)/L(1 - s, π^ι × (π')^ι)
    = ω_(π')(-1)^(r-1) ε(s, π × π', ψ) Ψ(s, W, W'; j)/L(s, π × π')`.
  For `t = r - 1` one has `j = k = 0` and `w_(r,r-1) = 1`.
- Section (3.1) and Theorem (3.1)(i), printed pages 404–405 (PDF pages 39–40):
  with `γ(s, π × σ, ψ) = ε(s, π × σ, ψ) L(1 - s, π^ι × σ^ι)/L(s, π × σ)`, for
  `σ` induced from representations `σᵢ` of Whittaker type,
  `γ(s, π × σ, ψ) = ∏ γ(s, π × σᵢ, ψ)`.

Apply Theorem (2.7)(2) with `π' = σ = Ind(χ₁, ..., χ_(r-1))`, `χᵢ` unramified
with `χᵢ(ϖ) = xᵢ`, and `W' = W(g; x; ψ̄)`; rewrite it with `γ` and apply
Theorem (3.1)(i). Then `ω_σ(-1) = ∏ χᵢ(-1) = 1` since `-1` is a unit, which is
why the sign is `1`; `L(s, π × χᵢ) = P(xᵢ q^(-s))⁻¹` and
`ε(s, π × χᵢ, ψ) = ε(s + uᵢ, π × 1, ψ) = c xᵢ^m q^(-ms)` for
`χᵢ = |·|^(uᵢ)`, `q^(-uᵢ) = xᵢ`, since twisting the rank-one test by an
unramified character shifts `s` in all the defining integrals; likewise
`L(1 - s, π^ι × χᵢ⁻¹) = Pdual(xᵢ⁻¹ q^(-(1-s)))⁻¹`. Multiplying out gives the
displayed equation. This derivation is given here only to explain the
constants; it is not a Lean proof, and the multiplicativity theorem it uses
occupies Sections 3–7 of JPSS 1983.

### Factors used

As in the published `EssentialVectorLevelStatement` and
`EssentialDualComparisonStatement`, the L-polynomials and the epsilon factor
are the JPSS 1983 pair factors of `π × 1` (and of the inverse-transpose
pullback `× 1`), not the Godement–Jacquet factors `P_π`, `ε_π` that the 1981
text writes. Display (3) is a consequence of the pair-factor theory, and in
that theory the factors of `π × χᵢ` are literally those of `π × 1` shifted by
the unramified twist, so the statement uses the pair factors directly and does
not depend on the comparison between pair and Godement–Jacquet factors (which
is a gap discussed in [`EssentialStatement`](EssentialStatement.md)). The
polynomial `Pdual` is the pair L-polynomial of `inverseTransposePullback π`
for `ψ.scale (-1)`; the source's `P_π̃` is that of the contragredient, which
the pullback models (Gelfand–Kazhdan), and the L-factor does not depend on the
additive character.

### The Jacquet 2012 correction

H. Jacquet, *A correction to Conducteur des représentations du groupe
linéaire*, Pacific J. Math. 260 (2012), 515–525 (registered source
`jacquet-2012-conductor-correction`). The error reported there concerns the
1981 argument for the existence of the essential vector (the ideal `I(π)`
after display (5), printed pages 209–210), not displays (1) and (3), which
are consequences of JPSS 1983. The present statement involves no essential
vector.

## Choices

- **Only unitary `x`.** The source itself reduces display (1) to `|xᵢ| = 1`,
  where `σ` is irreducible and generic, and that is the case used in
  the source. Every unit tuple is allowed, including tuples with repeated
  entries.
- **Every `v`.** Display (3) holds for every `W` of the model, so the
  statement quantifies over every vector `v`; it does not mention essential
  vectors. A consumer applies it to an essential vector.
- **Spherical functions only.** The statement uses the explicit spherical
  functions `W(g; x; ψ̄)` and `W(g; x⁻¹; ψ)` rather than an arbitrary
  representation `σ` of `GL_(n+1)(F)`, so it needs no model of the induced
  representation and no identification of its Whittaker functions.
- **Fixed `ℓ'`.** As in `EssentialDualComparisonStatement`, the dual model uses
  the specific functional `ℓ'` with `ℓ'.val = (dualFunctional ψ π ℓ).val`, so no
  multiplicity-one or contragredient identification is assumed.
- **Hypotheses on the factors.** The epsilon factor `(c, m)` and the
  L-polynomials `P` and `Pdual` are hypotheses, not conclusions; the statement
  is vacuous if they do not exist. They are unique by the published `.unique`
  lemmas, so the statement is about the factors of `π`.
- **Existence of `R` and `Rdual`.** The rationality of the two integrals is
  part of the conclusion (JPSS 1983, Theorem (2.7)(ii)); it is not assumed.

## What this statement does not supply

It does not give the existence of the L-polynomials or of the epsilon factor,
nor anything about essential vectors. It does not state the functional
equation for non-spherical `W'`, nor for non-unitary `x`, nor in the formal
power series form of display (1).

## Intended use

Task 5548 proves `EssentialDualComparisonStatement` from this statement and
the mirabolic restriction injectivity of generic representations. For an
essential vector `w` of `π` (identity `∏ P(xᵢ q^(-s))⁻¹`) the statement with
`v` the vector of `w` makes the dual integral of `W̃` against `W(g; x⁻¹; ψ)` a
monomial times `∏ Pdual(xᵢ⁻¹ q^(-(1-s)))⁻¹`; the essential vector of the dual
model, translated by `diag(ϖ^m, ..., ϖ^m, 1)`, has the same integrals up to
one constant, which gives JPSS 1981 (5.3) after separation over unit `x`.

## Imports

Only the published `Langlands.Representation.Conductor.EssentialStatement`,
whose import closure supplies `IsJacquetNormalization`, `IsPairEpsilonFactor`,
`IsCharacterLPolynomial`, `rankOneQuotientHaar`, `rankOneCharacter`,
`IsSelfDual`, `coefficientMap`, `inverseSphericalWhittaker`,
`CorankOneConverges`, `corankOneIntegral`, `HasRationalContinuation`,
`NormalizedFunctionalEquation`, `dualFunctional`, `inverseTransposePullback`
and `UnitaryAdditiveCharacter.scale`.

## Lean checks

The module compiles with `lean_check` in environment `bb168ec3` with no
errors or warnings. The declaration was inspected: it returns `Prop`, has
universe parameters `uF uV`, and uses only `propext`, `Classical.choice` and
`Quot.sound`. There is no `sorry` and no new axiom.
