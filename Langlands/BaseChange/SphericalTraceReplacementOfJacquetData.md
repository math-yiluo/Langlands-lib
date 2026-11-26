# Replacing regular elementary tests by spherical tests in finite local trace sums

`SphericalTraceReplacementOfJacquetDataStatement` uses actual irreducible
admissible local representations, the canonical spherical Haar measures,
and the unramified base-change homomorphism. On the extension side each
trace is twisted by an intertwiner acting as the identity on the spherical
fixed vectors. On the base side the trace is ordinary.

The inducing tuples specify the spherical spectra on the constituents
with spherical vectors. The other local inputs give the Jacquet exponent
multisets with `HasWeylJacquetSupport` and the regular elementary traces
with `HasJacquetElementaryTraceExpansion`. In the latter input a common
nonzero factor multiplies the character evaluations. The ordinary weight
is scaled by the extension degree. Under these hypotheses a weighted
identity for the actual elementary pairs implies the same identity on
all pairs `(φ, b φ)` of spherical tests.

The proof takes the finite union of the extension spectra and the
powered base spectra. It uses the Satake character of each label to
compute the spherical distributions. A constituent with zero spherical
fixed space contributes zero. For an ordinary spherical constituent, the
Satake characterization of `b` gives the extension character at the
powered label. These are the spherical trace hypotheses of
`weylSphericalTraceReplacement`, which proves the weighted identity.

This internal reduction implements the algebraic end of Henniart–Lemaire,
*Changement de base et induction automorphe pour GLₙ en caractéristique non
nulle* (2011), I.5.5, Théorème and Lemma 2, printed pp. 37–39 (PDF pp. 45–47).
The local Jacquet expansions and their opposite-order support conditions
are inputs.

Source ID `provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61`,
SHA-256 `7af2940c75a75937c1bf9096eb329931d4245cf592e3572db0ff93ec6e76c5e0`.
