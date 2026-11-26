# The σ-lift character identity from two analytic inputs

The module `Langlands.BaseChange.SigmaLiftCharacterIdentity.Reduction` proves three
implications between statements of the Library.

## Concordant test functions

`concordantIntegralEquality_of_integrable` proves
`ConcordantIntegrableIntegralEqualityStatement.{u, v} → ConcordantIntegralEqualityStatement.{u, v}`.
A Schwartz–Bruhat function is continuous with compact support, hence integrable for a Haar
measure (`SchwartzBruhat.integrable`). The statement for integrable functions therefore
applies to concordant test functions. The extra hypothesis `CharZero F` of the second
statement is not used.

## Ordinary characters as twisted characters in degree one

`characterLocalIntegrability_of_twisted` proves
`TwistedCharacterLocalIntegrabilityStatement.{u, u, uV} → CharacterLocalIntegrabilityStatement.{u, uV}`.
Take the cyclic algebra `E = F` with `σ = 1` and `l = 1` (`isCyclicAlgebra_one`) and the
identity intertwiner of `ρ` with `ρ ∘ entrywiseAut 1 = ρ`. The twisted character for the
identity endomorphism is the ordinary character, so a twisted character function is a
character function (`isTwistedCharacterFunction_one_iff`). A regular semisimple `γ` is
σ-regular for `σ = 1`, `l = 1`: its cyclic norm is `γ` itself, which equals its base change
to `F`. So the local constancy at σ-regular points gives local constancy at regular
semisimple points.

## The reduction

`SigmaLiftCharacterIdentityReductionStatement.{u, v, uV, uW}` is the implication

- `ConcordantIntegrableIntegralEqualityStatement.{u, v}` (equality of the integrals of
  integrable concordant functions on `GL_n(E)` and `GL_n(F)`),
- `TwistedCharacterLocalIntegrabilityStatement.{u, u, uV}` (used in degree one, for the
  characters of `GL_n(F)` on spaces in universe `uV`),
- `TwistedCharacterLocalIntegrabilityStatement.{u, v, uW}` (for the twisted characters of
  `GL_n(E)` on spaces in universe `uW`)

`→ SigmaLiftCharacterIdentityStatement.{u, v, uV, uW}`.

`sigmaLiftCharacterIdentityReduction` proves it. The forward implication is
`sigmaLiftCharacterIdentityForward`. Its premises are supplied as follows:

- the two instances of `TwistedCharacterRegularValuesStatement` by
  `TwistedCharacterLocalIntegrabilityStatement.regularValues`;
- `RegularTransferStatement` by `regularTransfer`;
- `ConcordantIntegralEqualityStatement` by `concordantIntegralEquality_of_integrable`;
- `SigmaLiftCharacterIdentity.SigmaRegularOpenStatement` by
  `SigmaLiftCharacterIdentity.sigmaRegularOpen_of_cyclicNormLemma cyclicNormLemma`.

The reverse implication is `sigmaLiftCharacterIdentityReverse`, with
`CharacterLocalIntegrabilityStatement` supplied by `characterLocalIntegrability_of_twisted`.

## Sources

Henniart–Lemaire, *Changement de base et induction automorphe pour GL_n en
caractéristique non nulle*, Mém. SMF 124 (2011), II.2.9–II.2.11, printed pp. 69–73. Their
proof of the Proposition of II.2.9 uses the transfer of regularly supported functions, the
Weyl integration formulas of II.2.10 and the local integrability of the ordinary and twisted
characters. The first premise of the reduction is the consequence of the two Weyl
integration formulas that both directions use. The other two premises are the local
integrability of characters, Clozel, *Characters of non-connected, reductive p-adic groups*,
Canad. J. Math. 39 (1987), Theorem 1, printed p. 153, with Arthur–Clozel 1989, Chapter 1,
Proposition 2.2, printed p. 11. The degree-one case is Harish-Chandra's theorem for `GL_n(F)`
(*Admissible invariant distributions on reductive p-adic groups*, 1999, Theorem 16.3,
printed p. 75).
