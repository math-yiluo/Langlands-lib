# Smooth slices of intertwining integrals from uniform growth

Module `Langlands.Global.AdelicIntertwiningSmoothSlicesReductionStatement` contains one
`Prop`-valued definition, `Langlands.Global.IntertwiningSmoothSlicesReductionStatement`, and no
theorems.

## The statement

`IntertwiningSmoothSlicesReductionStatement.{u}` is the implication

```
AutomorphicFunctionUniformGrowthStatement.{u} → IntertwiningSmoothSlicesStatement.{u}
```

between two published propositions at the same universe:

- `AutomorphicFunctionUniformGrowthStatement` (module
  `Langlands.Automorphic.GroupSchemeAutomorphicFunctionUniformGrowthStatement`): functions
  automorphic on `Γ \ G(𝔸)` in the sense of `IsAutomorphicFunctionOn` have uniformly moderate
  growth, one exponent bounding all enveloping derivatives of their infinite slices, for a closed
  representation of positive size and a maximal compact subgroup of the infinite points;
- `IntertwiningSmoothSlicesStatement` (module `Langlands.Global.AdelicIntertwiningAutomorphyStatement`):
  for the data of `IntertwiningUniformAutomorphyStatement` there is `R₀` such that for every
  `R₀`-regular `λ` every infinite slice of `M(w, λ)φ` is plot-smooth.

## Sources and provenance

The implication is derived. Mœglin–Waldspurger, *Spectral decomposition and Eisenstein series*
(1995), registered as `moeglin-waldspurger-1995-spectral-decomposition`, II.1.6, Proposition (i),
printed pp. 87–88 (chapter PDF `06.1_pp_78_100_Definitions.pdf`, PDF pp. 10–11), asserts that for
sufficiently regular parameters the intertwining integral converges absolutely and uniformly on
compact sets and defines an automorphic form, in particular a smooth one. Its proof on p. 88 bounds
the absolute integral by the integral over the compact quotient `U'(k) \ U'(𝔸)` of an Eisenstein
sum and applies the convergence result II.1.5; it does not discuss derivatives. The conclusion of
`IntertwiningSmoothSlicesStatement` is the smoothness aspect of that automorphy assertion, in the
infinite variable, for the Library's regularity condition and normalization.

The premise records what a proof of that smoothness by differentiation under the integral needs
beyond convergence. The factor `m_P(·)^λ` of the integrand and the factor `m_Q(·)^{-wλ}` of the
operator must be smooth; the Library proves this for every maximal compact `K`
(`Langlands.Global.adelicSmoothIwasawaHeight`), so it is not a premise. All derivatives of the
inducing form must have moderate growth with one exponent, so that one regularity threshold gives
an integrable majorant for every derivative of the integrand. This is uniformly moderate growth in
the sense of Mœglin–Waldspurger I.2.3 (printed p. 25, chapter PDF
`05.2_pp_18_40_Automorphic_forms_growth_constant_terms.pdf`, PDF p. 8), which they derive for
automorphic forms on `U(𝔸) M(k) \ G` at the end of I.2.17 (printed pp. 38–39, PDF pp. 21–22) from
I.2.5, Lemma (a) (printed p. 27, PDF p. 10). `AutomorphicFunctionUniformGrowthStatement` states it
for every left subgroup `Γ`; the proof `Langlands.Global.intertwiningSmoothSlicesReduction` uses it
for `Γ = U(𝔸) M(F)`.
