# Character coefficients along subgroups with compact rational quotient

Internal helper module for `UnequalUnfoldingReduction.md`. It studies
the Library coefficient `subgroupCharacterCoefficient F G U χ f`
(`GeneralLinearGlobalWhittaker`), the integral of
`f(u g) conj(χ(u))` over `U(F) \ U(𝔸)` against
`normalizedRationalQuotientHaarMeasure`, for a group scheme `G` and a
subgroup functor `U` with closed adelic points. Provenance: internal.

- `rightTranslateMeasurableEquiv`: right translation on a left coset
  space as a measurable equivalence.
- `coefficientIntegrand`, `subgroupCharacterCoefficient_eq_integral`:
  the integrand on the rational quotient (definitional unfolding).
- `subgroupCharacterCoefficient_mul_left`: if `U(F) \ U(𝔸)` is compact,
  `χ` is multiplicative, trivial on `U(F)`, of absolute value one, and
  `f` is left `U(F)`-invariant, then for `u ∈ U(𝔸)` the coefficient
  satisfies `W(u g) = χ(u) W(g)`. The proof uses the Library's right
  invariance of the quotient measure for compact quotients.
- `subgroupCharacterCoefficient_eq_setIntegral`: for measurable,
  left `U(F)`-invariant `χ` and `f`, the coefficient equals the mass
  normalizer times the integral of `f(n g) conj(χ(n))` over the chosen
  Borel fundamental domain of `U(F)` in `U(𝔸)`.
- `measurable_subgroupCharacterCoefficient`: under the same hypotheses
  the coefficient is a measurable function of `g`.
