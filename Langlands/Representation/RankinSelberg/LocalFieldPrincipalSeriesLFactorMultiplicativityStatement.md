# L-factor multiplicativity for unramified principal series over every local field

This module states one proposition and proves nothing:
`Langlands.RankinSelberg.LocalFieldPrincipalSeriesLFactorMultiplicativityStatement`.
It is the L-factor companion of
`Langlands.RankinSelberg.LocalFieldPrincipalSeriesGammaMultiplicativityStatement`
(part (i) of the same theorem), with the same hypotheses.

## Source

Jacquet, Piatetski-Shapiro and Shalika, *Rankin–Selberg convolutions*, Amer. J.
Math. 105 (1983), Theorem (3.1)(ii), printed pages 404–405 (source
`jpss-1983-rankin-selberg`, PDF pages 39–40, read from the scan). Let `π` be a
representation of Whittaker type of `GL_r(F)`, and let
`σ = Ind(G_t, Q; σ_1, …, σ_p)` be induced from representations `σ_1, …, σ_p` of
Whittaker type on the blocks of the *lower* standard parabolic subgroup `Q` of
`GL_t(F)` of type `(t_1, …, t_p)` (display (3.1)(1)). Then

`L(s, π × σ) ∈ ∏_{1 ≤ i ≤ p} L(s, π × σ_i) ℂ[q^(-s), q^s]`.

Section 0.3 (printed page 375) takes the ground field to be any nonarchimedean
local field. The statement here is the special case in which every block has size
one and every `σ_i` is an unramified character, so that `σ` is an unramified
principal series of `GL_(n+1)(F)`.

The Library's `principalSeries hϖ n hq z` induces `(χ_{z_0}, …, χ_{z_n})` from the
*upper* triangular Borel subgroup `B`, whereas the source induces from the lower one
`B⁻`. Let `w₀` be the antidiagonal permutation matrix. Then `f ↦ (g ↦ f(w₀ g))` is a
`GL_(n+1)(F)`-isomorphism from the induction from `B` of `(χ_{z_0}, …, χ_{z_n})` onto
the induction from `B⁻` of the reversed tuple `(χ_{z_n}, …, χ_{z_0})`, because
`w₀ B⁻ w₀⁻¹ = B` reverses the diagonal and matches the modulus characters. The
product on the right of (ii) does not depend on the order of the factors. Hence
the statement below is the source's (3.1)(ii) for the lower-Borel induction of
`(χ_{z_n}, …, χ_{z_0})`, transported along this isomorphism (L-polynomials are
invariant under equivalences: `IsGeneralSymmetricLPolynomial.congr_equiv`).

### From the ideal statement to the polynomial identity

Write `X = q^(-s)`, `L(s, π × I(z)) = 1 / P(X)` and `L(s, π × χ_{z_i}) = 1 / P_i(X)`,
with `P(0) = P_i(0) = 1`. Then (ii) says that `∏_i P_i / P` lies in `ℂ[X, X⁻¹]`,
that is, `X ^ e * ∏_i P_i = Q * P` for some `e : ℕ` and some polynomial `Q`. This is
the form of the Library's p-adic statement
`Langlands.RankinSelberg.LFactorMultiplicativityStatement`
(module `RankinSelberg/MultiplicativityStatement`), which the conclusion copies.

The Library states the full theorem only for the canonical p-adic fields. That
statement takes `F : PadicField p` and the p-adic block induction
`canonicalNormalizedProductInduced`, which is not defined for other fields. This
module replaces both: `F` is an arbitrary nonarchimedean local field of any
characteristic, and the induced representation is the published general-field
unramified principal series.

## The statement

`LocalFieldPrincipalSeriesLFactorMultiplicativityStatement` quantifies over:

- a nonarchimedean local field `F`
  (`[Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]`),
  Hausdorff and totally disconnected (`[T2Space F] [TotallyDisconnectedSpace F]`;
  every such field has both properties, and `IsSelfDual` requires them as
  instances), with the Borel σ-algebra `borel F`;
- `q` with `hq : Conductor.UnramifiedPrincipalSeries.IsResidueCardinality q`, that is,
  `q` is the cardinality of the residue field;
- an absolute value `abv : AbsoluteValue F ℝ` and a unit `ϖ` with
  `hϖ : IsUniformizingElement (ValuativeRel.valuation F) ϖ`, such that
  `abv ϖ = q⁻¹` and `abv x = 1` for every `x` of valuation `1`. Thus `abv` is the
  normalized absolute value `|·|_F`;
- an additive character `ψ : UnitaryAdditiveCharacter F` and a Haar measure
  `ν : AdditiveHaarMeasure F` self-dual for `ψ` (`IsSelfDual ψ ν`). This forces
  `ψ` to be nontrivial, as JPSS require. In `IsPairLPolynomial`, `ν` enters only
  through the product measure on the `j × (n+1)` matrix variable of the
  unequal-rank integrals with `j > 0`, and rescaling `ν` rescales those integrals
  by a nonzero constant, so mathematically the L-polynomials do not depend on `ν`
  (this module proves nothing about it). The self-duality hypothesis is kept so that
  this statement and the gamma statement (part (i)) have the same hypotheses;
- ranks `r, n : ℕ` and a representation `π` of `GL_(r+1)(F)` on a complex vector
  space `V` in an independent universe `uV`, of Whittaker type for the standard
  character (`IsOfWhittakerType r (standardCharacter ψ r) π`: admissible, finitely
  generated, and with a one-dimensional space of `ψ`-Whittaker functionals);
- a tuple `z : Fin (n + 1) → ℂˣ` of Satake parameters, with no unitarity or
  regularity condition.

Its conclusion: there are `P : ℂ[X]` and `Pi : Fin (n + 1) → ℂ[X]` with

1. `IsGeneralSymmetricLPolynomial q ψ abv ν π (principalSeries hϖ n hq z) P`:
   `L(s, π × I(z)) = 1 / P(q^(-s))`;
2. for every `i`,
   `IsGeneralSymmetricLPolynomial q ψ abv ν π (rankOneCharacter (character hϖ (z i))) (Pi i)`:
   `L(s, π × χ_{z_i}) = 1 / Pi i (q^(-s))`;
3. `X ^ e * ∏ i, Pi i = Q * P` for some `Q : ℂ[X]` and `e : ℕ`.

Here:

- `Conductor.UnramifiedPrincipalSeries.character hϖ z : Fˣ →* ℂˣ` is the unramified
  character `a ↦ z ^ ord(a)`, so `χ_z(ϖ) = z` and `χ_z` is trivial on units;
- `rankOneCharacter χ` is the one-dimensional representation `χ ∘ det` of `GL_1(F)`;
- `Conductor.UnramifiedPrincipalSeries.principalSeries hϖ n hq z` is right
  translation on the normalized induction from the upper triangular Borel subgroup
  of the character `diag(a_0, …, a_n) ↦ ∏ χ_{z_i}(a_i)`, twisted by `δ^(1/2)`
  (computed with the residue cardinality `q`). By the isomorphism described under
  "Source", it is the source's `Ind(G_(n+1), Q; χ_{z_n}, …, χ_{z_0})` for the lower
  Borel subgroup `Q`;
- `IsGeneralSymmetricLPolynomial` (module `RankinSelberg/GeneralPairLFactor`) is the
  published JPSS L-polynomial relation `IsPairLPolynomial` with the Borel
  σ-algebras, required for every compatible quotient measure (one of which exists),
  and taken with the larger rank first (`π` first if `n ≤ r`, otherwise `σ` first).
  This is the convention that `LFactorMultiplicativityStatement` uses through
  `IsPadicSymmetricLPolynomial`, and that JPSS §2.12 (printed page 403) uses for
  pairs with the smaller rank first.

## Remarks on the scope

- Every `I(z)` is of Whittaker type, whether or not it is irreducible, so the
  source's hypotheses on the `σ_i` hold. No condition on `z` is imposed.
- The existence of `P` and of the `Pi i` is part of the conclusion, as in
  `LFactorMultiplicativityStatement`. It is JPSS 1983, Theorem (2.7), for the pairs
  `(π, I(z))` and `(π, χ_{z_i})`.
- The field parameters (`q`, `ϖ`, `abv`) are exactly the fields `residueCardinality`,
  `uniformizer`, `abv_uniformizer` and `abv_unit` of `Conductor.IsJacquetNormalization`,
  so a consumer working under that structure can apply the statement directly. No
  conductor condition on `ψ` is imposed.
- The statement does not assert the equality `L(s, π × I(z)) = ∏ L(s, π × χ_{z_i})`,
  which needs more hypotheses on `π` and an ordering of `z` (JPSS (8.4), (9.4)).
