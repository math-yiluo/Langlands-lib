# Entrywise interfaces for Whittaker prerequisites

Worker 118 authors these internal adapters for the published
`Langlands.WhittakerPrerequisitesStatement`. They derive directly from the
existing definitions and proved constructions in `Whittaker.GeneralLinear`,
`Whittaker.CharacterChange`, and `Whittaker.Algebraic`; no new external
mathematical assertion or source interpretation is introduced.

`UnitaryAdditiveCharacter.ofComplex` packages a continuous, nontrivial
complex-valued additive character of unit norm as the existing circle-valued
character. Its complex projection is the original character, definitionally.
Continuity is continuity into a subtype; nontriviality follows by projection.

`EntrywiseEquivariant` repeats the exact covariance equation in the target,
for the actual general linear group of rank `n + 1`. The sum defining the
bundled standard character equals the entrywise product by finite induction
and the additive character law. Bundled functional membership is equivalent
to this predicate because upper-unipotent membership is precisely the lower
entry and diagonal conditions. Rank one is included through empty sums and
products. Field and vector-space universes are independent.

The coefficient injectivity proof packages the functional and uses the
already constructed `modelEquiv`; equality of raw functions gives equality
in its nested subtype. It requires irreducibility and a nonzero functional,
with no admissibility premise. The character-existence equivalence transports
functionals through `characterChangeFunctionalEquiv`; injectivity in both
directions preserves nonzero functionals. Scaling by `-1` identifies the
complex character with its inverse. This changes the character on the same
representation, and does not assert genericity of all irreducibles.

`raw_exists_inverse_iff` and `raw_coefficient_injective` expose these results
with the original raw-character hypotheses. These adapters prove the second
and third clauses after conversion of the raw character. Multiplicity one remains a separate theorem obligation; this
module does not prove the full prerequisites proposition.
