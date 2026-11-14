# The standard L-polynomial of a generic representation over every local field

Author: Worker 5220; Worker 8 removed two lemmas that the Library now provides.
Internal helper module for the proof of
`Langlands.Conductor.SphericalCorankOneConvergenceStatement`; it introduces no
statement.

## Results

- `rankOneIdentityFunctional`, `rankOneIdentityFunctional_ne_zero`: the identity
  of `ℂ` is a nonzero inverse-character Whittaker functional for the trivial
  character of `GL₁`.
- `exists_isCharacterLPolynomial_one`: with exactly the binders of the target,
  under Jacquet's normalizations `h`, a generic `π` of `GL_(n+2)(F)` has `P` with
  `IsCharacterLPolynomial q ψ abv (rankOneQuotientHaar F) 1 π P`.

The proof uses two published lemmas of
`Langlands.Representation.Conductor.TrivialCharacterEpsilonReduction`:
`rankOneCharacter_one_isSmooth` (the trivial character of `GL₁` is smooth) and
`isOfWhittakerType_of_isGeneric_localField` (over every nonarchimedean local field
a generic representation is of Whittaker type, by `whittakerTypeFromMultiplicity`
and Gelfand–Kazhdan multiplicity one `localFieldMultiplicityOne`).

## Proof of `exists_isCharacterLPolynomial_one`

1. The Borel structures on `GL₁` and `N₁ \ GL₁` are replaced by `borel`
   (`BorelSpace.measurable_eq`, with `h.borel_rankOne`), and the published
   `AllField.RankinSelberg.eq_normalizedAbsoluteValue_ofInstances` and
   `residueCardinality_ofInstances` identify `abv` and `q` with the normalized
   absolute value and residue cardinality of `LocalFieldData.ofInstances F`.
2. The published all-field JPSS theorem
   `AllField.RankinSelberg.unequalRankCommonGenerator F (ofInstances F) 0 (n+1)`,
   applied with the compatible measure `rankOneQuotientHaar F`
   (`rankOneQuotientHaar_isCompatible`), an additive Haar measure on `F`, `π`, the
   trivial character of `GL₁` (Whittaker type by `scalar_isOfWhittakerType_rankOne`
   and `isOfWhittakerType_standard_iff_inverse`) and the functionals above, gives
   `P` generating every block of rational values `unequalRankValuesAt`.
3. For each block, after substituting the rank equation, the analytic conclusion
   `AllField.RankinSelberg.unequalRankAnalytic` and
   `UnequalRankAnalyticConclusion.zetaValues_eq` identify these values with
   `unequalRankZetaValuesAt`, so `P` is an `IsPairLPolynomial`
   (`isPairLPolynomial_of_lt`).
4. `IsPairLPolynomial.isCharacterLPolynomial` extracts the character generator.

## Provenance

JPSS 1983, Theorem (2.7) (literature ID `jpss-1983-rankin-selberg`), for the pair
`π × 1`, through the Library's all-field port of the JPSS development; recalled in
Jacquet 2012 (literature ID `jacquet-2012-conductor-correction`), section 1.
