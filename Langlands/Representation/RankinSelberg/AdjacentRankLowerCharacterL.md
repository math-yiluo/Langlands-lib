# Adjacent-rank lower L divisibility for every character

This internal composition proves the lower ordered-pair assertion needed by
`adjacentRankUpperL_of_lowerCharacter`. It is derived from the named analytic
and transport results below; it does not introduce another source assertion.
The field, the first-block carrier, and the test carrier have independent
universes. Both representations are arbitrary full Whittaker-type inputs.

For a representation `σ` of GL(r+1), a test representation `τ` of GL(r+1),
and an arbitrary quasicharacter `χ`, `AdjacentRankLowerCharacterL` uses the
actual normalized opposite-parabolic induction of the ordered blocks
`(σ, rankOneExtensionCharacter F χ)`. It asserts complete symmetric L
certificates for `(τ, induced)`, `(τ, σ)`, and `(τ, χ)`, with polynomials
`P`, `P₀`, and `P₁`, and

```
X ^ e * (P₀ * P₁) = Q * P.
```

`adjacentRankLowerCharacterL` proves this proposition for the supplied
self-dual Haar measure. Its conclusion retains the entire
`IsPadicSymmetricLPolynomial` predicates, including their existence witnesses
and quantification over compatible quotient measures and functionals.
There is no character-size restriction in the conclusion.

The implemented proof proceeds as follows.

1. Use the actual predecessor-size family `![r, 0]` and
   `adjacentLowerPairBlocks`. The rank-one extension has full Whittaker type,
   so the two blocks satisfy the required full-type hypotheses.
   `adjacentLowerPair_fixedRealRayCertificates` supplies fixed complete block
   certificates and the actual deformed induced certificates on one real ray.
2. The private coefficient-zero lemma unfolds a complete symmetric
   certificate, selects its witnessed compatible measure, and applies
   `IsPairLPolynomial.coeff_zero`. Thus both block polynomials have constant
   coefficient one, and their product is nonzero.
3. `secondBlockZero_isOfWhittakerType` supplies full type for the actual
   zero-parameter induced representation. Select a nonzero functional from
   that full type and a nonzero functional on `τ` for the scaled character
   `ψ.scale (-1)`. `symmetricLPolynomialExists` supplies a complete induced
   certificate. Its pair certificate supplies an actual compatible quotient
   measure and the required right-invariance instance.
4. For every actual coefficient of the selected test functional,
   `secondBlock_realRayClearing_of_certificates` converts the fixed complete
   real-ray certificates into formal clearing. The conversion uses the
   inverse-standard-character coefficient adapter without changing the
   actual coefficient function.
5. Apply `secondBlock_polynomialDivisibility_at_zero`, discharging its
   deformation premise with the published theorem
   `twoBlockSecondWhittakerDeformation`. This specializes the actual
   coefficient clearing and yields precisely the displayed polynomial
   identity. Its coefficient-uniqueness input is already discharged in the
   certified real-ray helper by the published
   `bilateralSpectralCoefficientUniqueness`.
6. Compose `secondBlockZeroEquiv` with the actual ordered shape/action
   equivalence `oppositeInducedEquiv_of_sizes`. Transport the complete
   induced certificate along this representation equivalence, and use the
   complete-certificate symmetry theorem to put `τ` first.

The underlying real-ray argument uses convergent spectral sums and finite
Laurent clearing; this composition does not cancel a polynomial on the
bilateral series module. The module proves the lower L assertion only.
The parent upper-family L theorem additionally needs the existing complete
ordered-family reversal, and the gamma assertion is separate.

Worker 1191 is credited for the included spectral-clearing bridge.
Workers 831 and 15 are credited for the included zero-comparison
construction in `AdjacentRankSecondBlockLDivisibility`. The published
second-block deformation theorem is reused by its Lean name.
