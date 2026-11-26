# Separation of essentially square-integrable traces on the regular elliptic set

`Langlands.BaseChange.EllipticDiscreteTraceSeparationStatement` concerns
`GL_n(F)` for a characteristic-zero nonarchimedean local field `F` and
`0 < n`. Fix a Borel Haar measure `μ`. Let `ρ i` be a finite family of
irreducible admissible essentially square-integrable complex representations
and let `π` be another such representation. If the trace distribution of `π`
agrees with a fixed complex linear combination of those of `ρ i` on every
Schwartz–Bruhat function supported in the regular elliptic set, then `π` is
equivalent to some `ρ i`.

The index type `I` has a `Fintype` instance. The carriers `V i` may vary
with `i`, and the family may contain repeated isomorphism classes. The field,
index type, family carriers, and carrier of `π` have independent universes.
The conclusion uses `Nonempty (π.Equiv (ρ i))` for the equivalence of
representations. The hypotheses use `IsEllipticSupported` for the support in
the locus of separable irreducible characteristic polynomials,
`JacquetLanglands.IsEssentiallySquareIntegrable` for square-integrability
modulo the center after a real determinant twist, and `Character.distribution`
for the trace with respect to `μ`.

## Derivation from elliptic character orthogonality

Harish-Chandra's character theorem gives locally constant character values on
the regular semisimple set. At each regular elliptic element, choose a compact
open neighborhood in the regular elliptic set where all the character
functions in the identity are constant. Testing against its indicator
multiplies each value by the same positive finite measure of the
neighborhood. Cancelling this factor yields the pointwise character identity
for the given Haar measure.

Multiplication by a scalar matrix preserves regular ellipticity. If `ω_τ`
is the central character of a representation `τ`, scalar translation by
`z ∈ Fˣ` multiplies its character value by `ω_τ(z)`. Apply the pointwise
identity to all such translates of a fixed regular elliptic element.
Linear independence of the distinct multiplicative characters of `Fˣ`
gives the identity with the sum restricted to representations with the
same central character as `π`.

For a representation made square-integrable modulo the center by the twist
`|det|⁻ˢ`, its original central character has modulus `|ϖ|_F^(ns)` at the
scalar matrix `ϖ I_n` for a uniformizer `ϖ`. Since `n > 0` and
`0 < |ϖ|_F < 1`, the common
central character fixes the real exponent `s` for all remaining
representations. Twisting each by the same `|det|⁻ˢ` multiplies every
character in the pointwise identity by the same function. The resulting
irreducible square-integrable representations have a common unitary
central character.

In Henniart–Lemaire II.4.8, formulas (1) and (2) give elliptic orthogonality
for the full central character when the extension is trivial. Pair the normalized
character identity with the normalized character of `π`. Its self-pairing
is one, and each pairing on the other side is zero unless the corresponding
representations are equivalent. Thus some term gives an equivalence, which
also holds after undoing the common twist.

## Sources

- G. Henniart and B. Lemaire, *Changement de base et induction automorphe
  pour GLₙ en caractéristique non nulle*, Mém. SMF 124 (2011).
  II.4.8, formulas (1) and (2), printed p. 90 (PDF p. 98), and the
  character rule for determinant twists on printed p. 91 (PDF p. 99).
  Literature ID `provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61`,
  SHA-256 `7af2940c75a75937c1bf9096eb329931d4245cf592e3572db0ff93ec6e76c5e0`.
- Harish-Chandra, *Admissible invariant distributions on reductive p-adic
  groups*, University Lecture Series 16, AMS (1999). Introduction and
  Theorem 16.3, printed pp. 1 and 75 (PDF pp. 16 and 90).
  Literature ID `harish-chandra-1999-admissible-invariant-distributions`,
  SHA-256 `d68d7fde0036e7236eaf84d356b1d793bd15b0109d1aaf5787ca4bf47fe6bb19`.
