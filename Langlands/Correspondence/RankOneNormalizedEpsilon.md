# Normalized spectral characters in rank-one arithmetic epsilon values

Worker 1555 derives this internal unit from the existing normalized reciprocity
predicate, actual continuous absolute-value power character, and bottom-field
character transport. It introduces no new original-literature assertion.

`CommonClosure.weilCharacter_normalizedAbsPowerCharacter` uses the supplied
`NormalizedReciprocity` hypothesis to identify the normalized absolute value
of each actual reciprocity unit with the base residue cardinality raised to
minus its actual base Weil degree. Evaluation of the absolute-value power,
followed by the real logarithm of an integer power and the integer-power
exponential identity, proves equality with the existing spectral character
at the unchanged complex parameter. Both residue cardinality and degree
remain those specified by `CommonClosureSpectral`.

`CommonClosure.fieldCharacterEquiv_spectralCharacter` applies the inverse
character-descent identity to this equality. It identifies the descended
spectral character over every finite intermediate field with that field's
actual normalized absolute-value power.

`baseFieldCharacterEquiv_normalizedAbsPowerCharacter` proves that canonical
bottom-field character transport preserves the absolute-value power. It
uses character and unit extensionality and the existing
`CanonicalTransport.normalizedAbs_map` for `baseFieldPadicEquiv`.

`fieldCharacterEquiv_normalized_rankOneSpectralProduct` combines the
preceding results with the compatible product-descent identity. The descent
of the spectral character times the two restricted standalone Weil
characters is the bottom-field transport of
`normalizedAbsPowerCharacter s * (χ * η)` on the original base field.
Both compatibility with standalone reciprocity and normalized common-closure
reciprocity are explicit premises of this character identity.

`conditionalPairEpsilonValue_of_normalized_rankOneBaseRestriction` rewrites
the existing full pair epsilon formula using that character identity.
It applies to every continuous actual bottom restriction of the two actual
rank-one Weil quotient classes, every supplied additive character, arbitrary
actual Haar measure, geometric Frobenius and complex spectral parameter.
Normalization comes from the supplied `IsSystem` proof. The result is the
bottom field's actual `abelianEpsilonExpression` at the transported character
`normalizedAbsPowerCharacter s * (χ * η)`. The preceding full formula already
includes the invariant-quotient determinant correction; this rewrite leaves
that convention intact.

`isArithmeticPairEpsilonFactor_normalized_rankOneWeilCharacterClass_iff`
rewrites the unchanged full arithmetic certificate by the same identity.
The right side retains existence of a transported nontrivial unitary
additive character and a measure satisfying the existing intrinsic Fourier
self-duality condition, and existence of a geometric Frobenius. It also
retains the universal identity for every such transported character and
self-dual measure and every `s : ℂ`, with the original base residue
cardinality, coefficient `c : ℂˣ` and exponent `m : ℤ` in the epsilon
monomial. The proof rewrites the previously established exact certificate
equivalence under these quantifiers.

The prime and base field remain arbitrary. The field universe `uF`,
parameter-carrier universe `uP`, and supplied-system universe `uV` remain
independent; actual common-closure pairs use the existing carrier universe
`max uF uV`. The reciprocity data, compatibility and validated system remain
explicit inputs. No family, assignment, additive character, measure,
Frobenius, monomial constants, analytic epsilon comparison or closed
supercuspidal correspondence proof is constructed.
