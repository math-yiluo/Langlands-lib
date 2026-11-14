# Proof of the spherical corank-one functional equation

Module `Langlands.Representation.Conductor.SphericalCorankOneFunctionalEquationProof`.

## Theorem

`Langlands.Conductor.sphericalCorankOneFunctionalEquation :
SphericalCorankOneFunctionalEquationStatement.{uF, uV}`. This is the Library statement
`Langlands.Conductor.SphericalCorankOneFunctionalEquationStatement` (module
`Langlands.Representation.Conductor.SphericalCorankOneFunctionalEquationStatement`). It is
JPSS 1983, Theorem (2.7), for `π × I(x)`, with the corank-one integrals taken against the
spherical functions `W(x; ψ̄)` for unitary `x`. It holds over every nonarchimedean local field,
including positive characteristic, at arbitrary universes `uF` and `uV`. The theorem has no
hypotheses, and its axioms are `propext`, `Classical.choice` and `Quot.sound`.

## Proof as implemented

The theorem applies `SphericalCorankOne.sphericalCorankOneFunctionalEquation_of_inputs`
(module `SphericalCorankOneReduction`) to three theorems:

1. `RankinSelberg.localFieldUnequalRankAnalytic.{uF, uV, 0}` (module
   `RankinSelberg/LocalFieldUnequalRankAnalyticReduction`): all-field JPSS 1983,
   Theorem (2.7)(i)–(ii), under the target's binders. It is obtained from the published
   all-field theorem `AllField.RankinSelberg.unequalRankAnalytic`.
2. `sphericalCorankOneConvergence.{uF, uV}` (published, module
   `Conductor/SphericalCorankOneConvergenceProof`): the standard L-polynomial of `π × 1` and
   convergence of the corank-one integrals against `W(x; ψ̄)` on right half-planes.
3. `SphericalCorankOne.principalSeriesGammaInput_of_multiplicativity` (module
   `SphericalCorankOneMultiplicativityBridge`) applied to the published
   `RankinSelberg.localFieldPrincipalSeriesGammaMultiplicativity.{uF, uV}` (JPSS 1983,
   Theorem (3.1)(i), for `π × I(z)` over every local field). The bridge combines it with the
   unramified twist of the rank-one gamma factor.

The reduction's Markdown describes the argument. It builds the rank-one gamma factor of
`π × 1` from convergence and the epsilon factor (`SphericalCorankOneRankOneGamma`). It then
forms the gamma factor of `π × I(x)` as a product of rescalings. The spherical function is
realized in `I(x)` through `exists_glInverseFunctional_sphericalWhittaker`
(`OrderedUnramifiedSphericalFunctional`). Finally the normalized functional equation is read
off from the gamma relation (`SphericalCorankOneSphericalEquation`, with the integral and
algebra lemmas of `SphericalCorankOneIntegrals` and `SphericalCorankOneGammaAlgebra`).

## Supporting modules in this contribution

- `Conductor/SphericalCorankOneGammaAlgebra`, `Conductor/SphericalCorankOneIntegrals`,
  `Conductor/SphericalCorankOneRankOneGamma`, `Conductor/SphericalCorankOneSphericalEquation`,
  `Conductor/SphericalCorankOneReduction`, `Conductor/SphericalCorankOneMultiplicativityBridge`,
  `Conductor/OrderedUnramifiedSphericalFunctional`;
- `Conductor/UnramifiedSphericalWhittaker` (Worker 5557, Task 5680 draft, split (b)):
  Shintani's formula for the spherical coefficient of every inverse-character functional on
  `I(z)`, and the trivial action of `-1`;
- `RankinSelberg/LocalFieldUnequalRankAnalyticStatement`,
  `RankinSelberg/LocalFieldUnequalRankAnalyticReduction`.
