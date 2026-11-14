# The spherical corank-one functional equation from a gamma factor

Module `Langlands.Representation.Conductor.SphericalCorankOneSphericalEquation`, namespace
`Langlands.Conductor.SphericalCorankOne`. It is an internal helper for the proof of
`Langlands.Conductor.SphericalCorankOneFunctionalEquationStatement`. It holds over every
nonarchimedean local field. No `PadicField` is involved.

## Statement

`normalizedFunctionalEquation_of_sphericalGammaFactor`. Let `F` be a nonarchimedean local field,
`q > 1`, `δ = q⁻¹`, `π` a representation of `GL_(n+2)(F)` and `σ` a representation of
`GL_(n+1)(F)`. Assume:

- `rationalGammaExpression δ C M Q Q̃` is a gamma factor of `π × σ`
  (`IsPairGammaFactor q ψ abv ν π σ`), with `Q̃ ≠ 0`;
- `μ` is a quotient measure compatible with the Haar measures;
- `ℓ` is a nonzero Whittaker functional on `π`, and `ℓ'` is its dual functional on the
  inverse-transpose pullback (`ℓ'.val = (dualFunctional ψ π ℓ).val`);
- `lam` is a nonzero inverse Whittaker functional on `σ`, and `-1` acts on the model of `σ`
  for `lam` by the scalar `1` (`HasModelMinusOneScalar σ lam 1`);
- `ψ` and `ψ.scale (-1)` are trivial on the ring of integers, `ϖ` is a uniformizer, and
  `x : Fin (n+1) → ℂˣ` is such that Jacquet's spherical function
  `inverseSphericalWhittaker hψ hϖ q x` lies in the model of `σ` for `lam`.

Then for every vector `v` of `π` there are rational functions `R`, `R̃` such that:

- `R` continues the corank-one integral of the coefficient of `v` for `ℓ` against
  `inverseSphericalWhittaker hψ hϖ q x`;
- `R̃` continues the corank-one integral, for `ψ.scale (-1)`, of the coefficient of `v` for `ℓ'`
  against `inverseSphericalWhittaker hψ' hϖ q x⁻¹`;
- `NormalizedFunctionalEquation q Q Q̃ 1 C 0 M R R̃` holds.

These are the last three conjuncts of the target statement, with scalar `1` and exponent `0`.

## Proof

- `ℓ'` is the published `firstDualFunctional ψ π ℓ` (subtype extensionality).
- `corankOne_gammaFunctionalEquation` (module `SphericalCorankOneIntegrals`), applied to the
  model functions `coefficientMap π ℓ v` and `inverseSphericalWhittaker hψ hϖ q x`, gives a
  scalar `ζ` with `HasModelMinusOneScalar σ lam ζ`, continuations `R`, `R̃` and the gamma
  functional equation. Since `lam ≠ 0`, the scalar is unique, so `ζ = 1`.
- `normalizedFunctionalEquation_of_gammaFunctionalEquation` (module
  `SphericalCorankOneGammaAlgebra`) turns the gamma functional equation for
  `rationalGammaExpression δ C M Q Q̃` into the normalized functional equation. Here `Q̃ ≠ 0`
  and `1 ^ (n+1) = 1` are used.
- In the continuation `R̃`, the published `firstDualFunction_coefficient` rewrites the first
  dual function as the coefficient of `v` for `ℓ'`. The second dual function of
  `inverseSphericalWhittaker hψ hϖ q x` is `inverseSphericalWhittaker hψ' hϖ q x⁻¹` by
  `secondDualFunction_inverseSphericalWhittaker` (published module `Conductor/SphericalDualParameters`).

## Provenance

The specialization of the local functional equation to Jacquet's spherical function, with the
dual function `W(·; x⁻¹; ψ)`, is Jacquet, Piatetski-Shapiro and Shalika, *Conducteur des
représentations du groupe linéaire*, Math. Ann. 256 (1981), Section (4.2), printed pages
208–209. The Lean proof is internal.
