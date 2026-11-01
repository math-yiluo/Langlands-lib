# Adjacent-image gamma factorization for arbitrary full-type tests

This internal result removes the test irreducibility hypothesis from
`adjacentRankImage_gammaFactorization_of_irreducible_test`. It proves the same
`AdjacentRankImageGammaFactorization` predicate: complete symmetric gamma
certificates for `(σ, τ)` and `(τ, rankOneCharacter χ)`, whose product is a
complete certificate for `(π, τ)`. It retains independent field, block, test and
ambient universes.

`adjacentRankImage_gammaFactorization` assumes full Whittaker type for all three
representations, specified nonzero block, ambient and inverse-character test
functionals, and equality of the entire actual adjacent model-map range with
the specified ambient coefficient range. The supplied scalar Haar measure is
self-dual, and the supplied quotient measure is compatible with the canonical
group and unipotent Haar measures. The chosen test may be reducible. Actual
ambient image realization and continuation in the second block remain separate
obligations; this result does not prove the closed adjacent-rank base statement.

The proof selects the irreducible generic socle `S` of the actual coefficient
image of the inverse-character test functional. The published generic-socle
theorem supplies its full Whittaker type, and submodel evaluation is nonzero.
Its coefficient model is contained in the original test coefficient model.
The irreducible-test theorem therefore constructs both block certificates and
the ambient product certificate for the socle test.

The published full-type construction independently supplies complete symmetric
gamma certificates for the original pairs. For `(σ, S)` and `(π, S)`, the
scaled-standard to inverse-character conversion preserves the underlying
functional and coefficient inclusion. The general fixed-functional gamma
comparison through model inclusion identifies each socle gamma value with the
corresponding original value.

For the character block, both test functionals are translated by the actual
diagonal character-change element at `-1`. The private inclusion helper proves
that this simultaneous translation preserves inclusion: each coefficient is
evaluated at the same left-translated group element. Translation is an invertible
linear map on functionals and hence preserves nonzeroness. Scaling twice by
`-1` restores the original character. The resulting standard-character model
inclusion compares `(S, rankOneCharacter χ)` with `(τ, rankOneCharacter χ)`.
Substitution of these three equalities into the existing original ambient
certificate yields the required product certificate.

The proof uses generic-socle existence, actual submodel coefficient inclusion,
character-change equivalences, and complete gamma certificates. It does not
identify a reducible original carrier with its coefficient model, invoke JPSS
multiplicativity, or cancel on unrestricted bilateral coefficient series.
