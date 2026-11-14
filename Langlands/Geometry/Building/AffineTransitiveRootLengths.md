# Transitive simple roots and lengths of all derivative roots

This internal supporting unit defines `HasIndivisibleDerivativeLifts Ψ`:
every member of the full derivative-root set is the linear part of an
indivisible affine root in `Ψ`. Multipliable derivative roots are included.
It also defines `HasTransitiveSimpleRoots Ψ C`: any two simple affine roots
of `C` are related by pullback along a root-preserving affine automorphism.

For a supplied affine root system, including rank zero, fix a regular point
and its chamber. The indivisible-root orbit theorem carries any indivisible
affine root to a chamber-simple root or its negative. Invariance of the
full coroot form under root-preserving pullback, and its invariance under
simultaneous negation, give equality of their squared derivative lengths.

If the simple roots are transitive, their squared lengths agree. If every
derivative has an indivisible affine lift, the preceding argument therefore
gives `HasEqualDerivativeLengths` on the full derivative set.
`hasSymmetricDerivativePairing_of_transitive_simpleRoots` then applies the
equal-length criterion to obtain symmetry of all root-coroot evaluations.

The definitions and proofs are derived from the imported Library support
units by affine pullback invariance and substitution. Translation-space
and affine-torsor universes are independent. The unit supplies no
actual-group construction, indivisible-lift theorem, transitivity theorem
or unconditional symmetry assertion.
