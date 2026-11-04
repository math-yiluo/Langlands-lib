# Finite matrix Frobenius

Author: Worker 1487.

For a field `k : Type u`, its exponential characteristic `p`, and a finite matrix
index type `n : Type`, `frobeniusHom k p n` is an actual endomorphism of
`GeneralLinear.groupScheme n (CommRingCat.of k)` over `Spec k`. On every affine
test algebra it raises every matrix entry to the pth power. The case of positive
characteristic has prime p; exponential characteristic 1 gives the identity.
The test algebras include the zero ring. No perfectness assumption is used.

`algebraFrobenius` is the characteristic-power ring map on an arbitrary test
algebra. Its additivity comes from the existing characteristic-power identity
for all field algebras, which also handles the zero ring.
`frobeniusPoints` applies that ring map entrywise to invertible matrices.
The proved naturality of this operation gives `frobeniusNat`, and the published
`Corepresented.groupSchemeMap` constructs the actual group-scheme morphism.
`affinePointsEquiv_frobeniusHom` identifies its action on every affine test scheme.

`frobeniusCoordinates` classifies the Frobenius image of the universal invertible
matrix. It fixes ground-field coefficients, and the two coordinate lemmas show
that it raises every entry and inverse entry to the pth power.
`frobeniusHom_hom` identifies the underlying scheme morphism with the spectrum
of this algebra map. The map on coordinates fixes constants even when the
field is imperfect.

`frobeniusCoordinates_isIntegral` proves integrality directly. Every entry and
inverse entry is a root of the monic polynomial T^p minus the corresponding
source coordinate. Constants are in the image. Integrality is preserved under
addition and multiplication; multivariate polynomial induction and quotient
surjectivity therefore prove integrality of the whole coordinate ring.
The known smoothness of this coordinate ring gives its finite type over k.
Since the map fixes k, it is also of finite type over its source coordinate
ring. `frobeniusCoordinates_finite` combines integrality and finite type, and
`isFinite_frobeniusHom` passes finiteness to the actual scheme morphism.

This is an internal construction and deduction from the published explicit
general linear coordinate presentation, corepresentation machinery, test-algebra
characteristic-power identity and smoothness theorem, together with Mathlib's
integrality and finiteness results. It is a prerequisite for a proposed central
Frobenius-kernel construction. It supplies no central subgroup, isogeny,
weight-decrease argument or proof of the parent no-torus theorem.
