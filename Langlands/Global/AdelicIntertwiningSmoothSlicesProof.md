# Smooth infinite slices of regular intertwining integrals: proof

Module `Langlands.Global.AdelicIntertwiningSmoothSlicesProof`. The theorem

```lean
theorem Langlands.Global.intertwiningSmoothSlices : IntertwiningSmoothSlicesStatement.{u}
```

proves the published statement `IntertwiningSmoothSlicesStatement` of the module
`Langlands.Global.AdelicIntertwiningAutomorphyStatement` (Mœglin–Waldspurger II.1.6 (i), smoothness).
The data are those of `IntertwiningUniformAutomorphyStatement`: a regular parabolic `P = MU`, a
second parabolic `Q = M'V`, a Weyl conjugation `(w, c)`, a maximal compact `K` in Iwasawa position
for both, and a function `φ` automorphic on `U(𝔸)M(F) \ G(𝔸)`. For these there is a real `R₀` such
that, for every `R₀`-regular `λ`, every infinite slice of `M(w, λ)φ` is plot-smooth. Lean reports
the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Proof

The theorem is the term

```lean
intertwiningSmoothSlicesReduction.{u}
  Langlands.Automorphic.GroupSchemeFunctions.automorphicFunctionUniformGrowth.{u}
```

- `Langlands.Global.intertwiningSmoothSlicesReduction` (module
  `Langlands.Global.AdelicIntertwiningSmoothSlicesReduction`) proves
  `IntertwiningSmoothSlicesReductionStatement`, the implication
  `AutomorphicFunctionUniformGrowthStatement → IntertwiningSmoothSlicesStatement`.
  - If the matrix embedding has size zero, the infinite points form a single point, so every
    infinite slice is constant and hence smooth.
  - In positive size, the reduction applies the premise to the subgroup `Γ = U(𝔸)M(F)`
    (`parabolicQuotientSubgroup`). This gives one growth exponent for all twisted derivatives of
    `φ`.
  - The reduction then chooses one regularity threshold from that common exponent, using the
    Eisenstein majorant `eisensteinGlobalMajorant`. It does so before the parameter and the finite
    point are fixed.
  - For each regular parameter, the Eisenstein estimate and the unfolding estimate
    `exists_integrable_unfolding_majorant` supply an integrable factor `B` on the integration
    quotient.
  - Each iterated derivative of the integrand is locally bounded in the infinite variable by a
    multiple of `B`. The multiplier may depend on the list of directions.
  - These bounds justify differentiation under the integral sign
    (`contMDiff_integral_of_dominated_invariantDerivatives`).
  - The height factor of the operator is smooth by `adelicSmoothIwasawaHeight`.
- `Langlands.Automorphic.GroupSchemeFunctions.automorphicFunctionUniformGrowth` (module
  `Langlands.Automorphic.GroupSchemeAutomorphicFunctionUniformGrowthProof`) proves
  `AutomorphicFunctionUniformGrowthStatement`. Its setting:
  - `G` is a connected reductive group over a number field;
  - `rho` is a closed matrix embedding of positive size;
  - `Kinf` is a maximal compact subgroup of the infinite points;
  - `Γ` is an arbitrary subgroup of `G(𝔸)`.

  Every function automorphic on `Γ \ G(𝔸)` in the sense of `IsAutomorphicFunctionOn` then has
  uniformly moderate growth. One exponent bounds every enveloping-algebra derivative of its
  plot-smooth infinite slices, and the constant may depend on the derivative. Mœglin–Waldspurger
  I.2.3 (printed p. 25) defines this condition with its common exponent. I.2.17 (printed pp.
  38–39) establishes it for automorphic forms on the parabolic quotients `U(𝔸)M(k) \ G`. The
  reduction applies the theorem only in positive size, with `Γ = U(𝔸)M(F)`.

The pages of those two modules describe the arguments.
