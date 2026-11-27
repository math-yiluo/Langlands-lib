# Spherical replacement for finite sums of generic local distributions

`RegularElementarySphericalTraceReplacementStatement` concerns a cyclic
unramified extension \(E/F\) of degree \(\ell\). In each of two finite
families, the representations are irreducible, admissible and Whittaker
generic. Each upper representation comes with an intertwiner for the
chosen generator. If the two weighted sums of character distributions
agree on every regular elementary pair, they agree on every spherical
pair \((\phi,b\phi)\). The trace on the upper side is the twisted trace
with the supplied intertwiner. The lower trace is ordinary.

The proof assumes `RegularElementaryJacquetTraceStatement` and
`UnramifiedWeylJacquetSupportStatement` at both fields. It also assumes
`UnramifiedGenericSigmaNormalizationStatement` at the upper field.
The fields, the representation carriers and the finite index types
have independent universes.

A spherical representation belongs to a principal series found by
its spherical Hecke spectrum and `sphericalHeckeComparison`. For a
representation with a nonzero integral-diagonal Jacquet fixed space,
`unramifiedJacquetDetection` gives an embedding into an unramified
principal series. The proof identifies the integral diagonal with
the norm-one singleton Levi by the order test on each diagonal entry.
If both fixed spaces vanish, the Jacquet multiset is empty and both
types of trace vanish. In that case any inducing tuple gives the
required support bounds.

For an upper principal-series subquotient the normalization proposition
gives an intertwiner fixing the Borel Jacquet quotient and every
spherical vector. An upper representation with both fixed spaces zero
already satisfies the required fixing conditions. The original
intertwiner differs from the resulting intertwiner by a scalar.
`twistedDistribution_smul` moves this scalar into the exterior
coefficient, uniformly for all tests.

`regularElementaryNormalizedJacquet` supplies the elementary expansions
with a common nonzero factor. The Weyl support proposition supplies the
multiset bounds, the full multiset for spherical contributors and the
opposite-order exclusion for the other contributors.
`sphericalTraceReplacementOfJacquetData` then gives the desired equality
of the spherical sums with the same rescaled coefficients.

This is the local trace separation of Henniart–Lemaire,
*Changement de base et induction automorphe pour GLₙ en caractéristique
non nulle* (2011), I.5.5, Théorème and Lemma 2, printed pp. 37–39
(PDF pp. 45–47). Section I.6.9, printed pp. 50–51 (PDF pp. 58–59),
uses it on the spectral side of the trace comparison.

Source ID `provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61`,
SHA-256 `7af2940c75a75937c1bf9096eb329931d4245cf592e3572db0ff93ec6e76c5e0`.
