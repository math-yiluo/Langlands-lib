# Reduction of the spherical corank-one functional equation to three inputs

Module `Langlands.Representation.Conductor.SphericalCorankOneReduction`, namespace
`Langlands.Conductor.SphericalCorankOne`. The main theorem of this module derives
`Langlands.Conductor.SphericalCorankOneFunctionalEquationStatement` from three propositions,
which it takes as hypotheses. The module
`Langlands.Representation.Conductor.SphericalCorankOneFunctionalEquationProof` proves all three
and so proves the target. No `PadicField` is involved.

## Definition

- `PrincipalSeriesGammaInput`: under the target's binders and Jacquet's normalizations `h`,
  for every generic `π` of `GL_(n+2)(F)`, every gamma factor `G` of `π × 1` and every unitary
  `x`, the product `∏ i, rationalRescale (x i) G` (that is, `∏ G(x_i X)`) is a gamma factor of
  `π × principalSeries h.uniformizer n h.residueCardinality x`. This is JPSS 1983,
  Theorem (3.1), for the unramified principal series, combined with the unramified twist.
  It is an internal interface. `SphericalCorankOneMultiplicativityBridge` proves it from the
  published `LocalFieldPrincipalSeriesGammaMultiplicativityStatement`.

## Statements

- `isOfWhittakerType_of_isGeneric_localField`: over every nonarchimedean local field, a
  representation that is generic for `ψ` is of Whittaker type for the standard character.
- `unequalRankConvergenceAt_of_analytic hA …`: from `LocalFieldUnequalRankAnalyticStatement`,
  for ranks `r + 1` and `n + 1` with `r = n + (j + k + 1)`, Whittaker type of `π` and inverse
  Whittaker type of `σ`, and nonzero functionals, the block `(j, k)` integrals converge on a
  right half-plane (`UnequalRankConvergenceAt j k hr`, measure `rectangularMeasure ν j (n+1)`).
- `prod_comp_ne_zero`: if `P.coeff 0 = 1`, then `∏ i, P.comp (C (x i) * X) ≠ 0`.
- `sphericalCorankOneFunctionalEquation_of_inputs`: the target
  `SphericalCorankOneFunctionalEquationStatement.{uF, uV}` follows from
  - `LocalFieldUnequalRankAnalyticStatement.{uF, uV, 0}` (all-field JPSS 1983, (2.7)(i)–(ii));
  - `SphericalCorankOneConvergenceStatement.{uF, uV}` (published statement: the standard
    L-polynomial of `π × 1` and convergence of the corank-one integrals against `W(x; ψ̄)` on
    right half-planes);
  - `PrincipalSeriesGammaInput.{uF, uV}`.

## Proofs

- Whittaker type: the published `whittakerTypeFromMultiplicity` applied to irreducibility,
  admissibility and the nonzero functional from `IsGeneric`. The span condition comes from the
  published all-field multiplicity one `localFieldMultiplicityOne`.
- Convergence: substitute `r`. Then the first conjunct of `UnequalRankAnalyticConclusion` is
  the claim.
- Nonvanishing: evaluate at `0`. Every factor has value `P(0) = P.coeff 0 = 1`.
- Main theorem. Fix the target's data, and let `δ = q⁻¹` and `1 < q`
  (`IsJacquetNormalization.one_lt_q`). The Borel instances on the quotients come from `h`.
  1. `π` and its inverse-transpose pullback `π̃` are generic
     (`isGeneric_inverseTransposePullback`), hence of Whittaker type. The trivial character of
     `GL_1` and its pullback are of inverse Whittaker type.
  2. `isPairGammaFactor_rankOne_of_convergence` gives the gamma factor
     `rationalGammaExpression δ c m P P̃` of `π × 1`. Its convergence hypotheses are
     `unequalRankConvergenceAt_of_analytic` at `n = 0`, `j = 0`, `k = n`, for `π × 1` and for
     `π̃ × 1̃` with the dual functionals.
  3. `PrincipalSeriesGammaInput` and `prod_rationalRescale_rationalGammaExpression` give the gamma
     factor `rationalGammaExpression δ (c^(n+1) (∏ x_i)^m) ((n+1) m) (∏ P(x_i X)) (∏ P̃(x_i⁻¹ X))`
     of `π × I(x)`.
  4. Unitary `x` has constant norms, so they are monotone.
     `exists_glInverseFunctional_sphericalWhittaker` (module
     `OrderedUnramifiedSphericalFunctional`) gives a nonzero inverse-character functional `lam`
     on `I(x)` whose coefficient of the spherical section is `inverseSphericalWhittaker … x`.
     That function therefore lies in the model of `lam`.
  5. The two convergence conjuncts are the convergence clause of
     `SphericalCorankOneConvergenceStatement`, applied to `(π, ψ, ℓ, x)` and to
     `(π̃, ψ.scale (-1), ℓ', x⁻¹)` with Jacquet's normalizations `h'`. The functional `ℓ'` is
     nonzero by `scaledDualFunctional_ne_zero`.
  6. `normalizedFunctionalEquation_of_sphericalGammaFactor` (module
     `SphericalCorankOneSphericalEquation`) gives the last three conjuncts. It uses the gamma
     factor of step 3, `prod_comp_ne_zero` and `lam`. The minus-one scalar `1` on the model
     of `lam` is `hasModelMinusOneScalar_principalSeries` (module
     `UnramifiedSphericalWhittaker`): `-1` acts trivially on `I(x)`.

## Provenance

The route is the one in Jacquet, Piatetski-Shapiro and Shalika, *Conducteur des
représentations du groupe linéaire*, Math. Ann. 256 (1981), Section (4.2), printed pages
208–209. It realizes `W(·; x; ψ̄)` in the induced representation `I(x)`. It then applies
JPSS 1983, Theorem (3.1), together with Theorem (2.7)(iii) for `π × 1`. The Lean
decomposition into these inputs is internal.

The generic-to-Whittaker-type implication reuses `Langlands.Conductor.isOfWhittakerType_of_isGeneric_localField` from [TrivialCharacterEpsilonReduction](TrivialCharacterEpsilonReduction.md).
