# Gamma multiplicativity for unramified principal series over every local field

This module states one proposition and proves nothing:
`Langlands.RankinSelberg.LocalFieldPrincipalSeriesGammaMultiplicativityStatement`.

## Source

Jacquet, Piatetski-Shapiro and Shalika, *Rankin–Selberg convolutions*, Amer. J.
Math. 105 (1983), Theorem (3.1)(i), printed pages 404–405. Let `π` be a
representation of Whittaker type of `GL_r(F)`, and let
`σ = Ind(G_t, Q; σ_1, …, σ_p)` be induced from representations `σ_1, …, σ_p` of
Whittaker type on the blocks of the *lower* standard parabolic subgroup `Q` of
`GL_t(F)` of type `(t_1, …, t_p)` (display (3.1)(1)). Then

`γ(s, π × σ, ψ) = ∏_i γ(s, π × σ_i, ψ)`.

The source states this over an arbitrary nonarchimedean local field. The
statement here is the special case in which every block has size one and every
`σ_i` is an unramified character, so that `σ` is an unramified principal series of
`GL_(n+1)(F)`.

The Library's `principalSeries hϖ n hq z` induces `(χ_{z_0}, …, χ_{z_n})` from the
*upper* triangular Borel subgroup `B`, whereas the source induces from the lower one
`B⁻`. Let `w₀` be the antidiagonal permutation matrix. Then `f ↦ (g ↦ f(w₀ g))` is a
`GL_(n+1)(F)`-isomorphism from the induction from `B` of `(χ_{z_0}, …, χ_{z_n})` onto
the induction from `B⁻` of the reversed tuple `(χ_{z_n}, …, χ_{z_0})`, because
`w₀ B⁻ w₀⁻¹ = B` reverses the diagonal and matches the modulus characters. The
right-hand product in (i) does not depend on the order of the factors. Hence the
statement below is the source's (3.1)(i) for the lower-Borel induction of
`(χ_{z_n}, …, χ_{z_0})`, transported along this isomorphism.

The Library already states the full theorem for the canonical p-adic fields
(`Langlands.RankinSelberg.GammaMultiplicativityStatement`, module
`RankinSelberg/MultiplicativityStatement`). That statement takes `F : PadicField p`
and uses the p-adic normalized block induction
`canonicalNormalizedProductInduced`, which is not defined for other fields. This
module replaces both: `F` is an arbitrary nonarchimedean local field of any
characteristic, and the induced representation is the published general-field
unramified principal series.

## The statement

`LocalFieldPrincipalSeriesGammaMultiplicativityStatement` quantifies over:

- a nonarchimedean local field `F`
  (`[Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]`),
  Hausdorff and totally disconnected (`[T2Space F] [TotallyDisconnectedSpace F]`;
  every such field has both properties, and the Fourier self-duality predicate
  `IsSelfDual` requires them as instances), with the Borel σ-algebra `borel F`;
- `q` with `hq : Conductor.UnramifiedPrincipalSeries.IsResidueCardinality q`, that is,
  `q` is the cardinality of the residue field;
- an absolute value `abv : AbsoluteValue F ℝ` and a unit `ϖ` with
  `hϖ : IsUniformizingElement (ValuativeRel.valuation F) ϖ`, such that
  `abv ϖ = q⁻¹` and `abv x = 1` for every `x` of valuation `1`. Thus `abv` is the
  normalized absolute value `|·|_F`;
- an additive character `ψ : UnitaryAdditiveCharacter F` and a Haar measure
  `ν : AdditiveHaarMeasure F` that is self-dual for `ψ` (`IsSelfDual ψ ν`). This
  forces `ψ` to be nontrivial, as JPSS require;
- ranks `r, n : ℕ` and a representation `π` of `GL_(r+1)(F)` on a complex vector
  space `V` in an independent universe `uV`, of Whittaker type for the standard
  character (`IsOfWhittakerType r (standardCharacter ψ r) π`: admissible, finitely
  generated, and with a one-dimensional space of `ψ`-Whittaker functionals);
- a tuple `z : Fin (n + 1) → ℂˣ` of Satake parameters, with no unitarity or
  regularity condition.

Its conclusion: there is `G : Fin (n + 1) → RationalFunctions` such that

1. for every `i`,
   `IsGeneralSymmetricGammaFactor q ψ abv ν π (rankOneCharacter (character hϖ (z i))) (G i)`:
   `G i` is the gamma factor `γ(s, π × χ_{z_i}, ψ)`, as a rational function of
   `X = q^(-s)`;
2. `IsGeneralSymmetricGammaFactor q ψ abv ν π (principalSeries hϖ n hq z) (∏ i, G i)`:
   the product is the gamma factor `γ(s, π × I(z), ψ)`.

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
- `IsGeneralSymmetricGammaFactor` (module `RankinSelberg/GeneralPairGamma`) is the
  published JPSS gamma relation `IsPairGammaFactor` with the Borel σ-algebras, taken
  with the larger rank first (`π` first if `n ≤ r`, otherwise `σ` first). This is
  the convention that `GammaMultiplicativityStatement` uses through
  `IsPadicSymmetricGammaFactor`. The relation asserts that the first representation
  has a nonzero `ψ`-Whittaker functional and the second a nonzero `ψ⁻¹`-Whittaker
  functional, and that the gamma functional equation with factor `G` holds for every
  compatible quotient measure and every pair of nonzero such functionals. So no
  multiplicity-one result for `I(z)` is needed to state it.

## Remarks on the scope

- Every `I(z)` is of Whittaker type, whether or not it is irreducible, so the
  source's hypotheses on the `σ_i` hold. No condition on `z` is imposed.
- The existence of the factors `G i` is part of the conclusion, as in
  `GammaMultiplicativityStatement`. It is JPSS 1983, Theorem (2.7), for the pairs
  `(π, χ_{z_i})`.
- The field parameters (`q`, `ϖ`, `abv`) are exactly the fields `residueCardinality`,
  `uniformizer`, `abv_uniformizer` and `abv_unit` of `Conductor.IsJacquetNormalization`,
  so a consumer working under that structure can apply the statement directly. No
  conductor condition on `ψ` is imposed.
- Part (ii) of Theorem (3.1), on L-factors, is not stated here.
