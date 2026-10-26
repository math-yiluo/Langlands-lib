# The alternating trace pairing and its two adjoint actions

For the actual algebra A of `CentralSimpleUnitaryData`, write sigma for its
involution. Given a unit beta of A, `tracePairing` constructs the rational
bilinear form

    psi_beta(x,y) = t(x beta sigma(y)),

where t is the normalized rational trace constructed in `RationalTrace`.
Thus its scalar factor is 1/n times the rational regular trace, with the
source-normalized real matrix-coordinate formula proved there.

If sigma(beta) = -beta, `tracePairing_isAlt` proves that this form is
alternating. The proof first applies involution invariance of t to its
argument and reverses the factors, obtaining
psi_beta(y,x) = -psi_beta(x,y). Over the rationals this makes every diagonal
value zero.

`tracePairing_nondegenerate` proves nondegeneracy for every unit beta,
without a skewness assumption. For left separation, the substitution
y = sigma(beta inverse times b) reduces to nondegeneracy of the regular
trace product pairing. For right separation, that pairing first forces
beta sigma(y) = 0; invertibility of beta and the involution then give y = 0.
The nonzero scalar 1/n preserves separation. Finite rational dimension
and simplicity follow from the actual central simple datum.

## The two adjoints

The generic construction `AlgebraInvolution.skewAdjoint` takes an algebra
involution fixing a commutative base ring, a unit beta, and
sigma(beta) = -beta. It constructs the actual base-linear, unital,
multiplication-reversing involution

    sigma_beta(b) = beta sigma(b) beta inverse.

Its involutivity follows from sigma(beta inverse) = -beta inverse.
For the rational involution of the datum, this is
`tracePairingAdjoint`.

`tracePairing_left` proves

    psi_beta(bx,y) = psi_beta(x,sigma(b)y).

This uses cyclicity of t. It needs no skewness assumption.
`tracePairing_right` proves, for skew beta,

    psi_beta(xb,y) = psi_beta(x,y sigma_beta(b)).

This follows by applying sigma to the beta-conjugated involution and
cancelling beta and its inverse. The theorem `tracePairing_bimodule`
combines these two identities. Right multiplication is the usual left
action of the opposite algebra, so this is the source's adjoint
compatibility for the commuting algebra and opposite-algebra actions.
`tracePairing_respectsInvolution` supplies the original left action's
compatibility to the existing PEL form interface.

## Provenance and scope

Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura
Varieties* (2001), Section I.7, printed p.52 (PDF p.60), defines the
pairing on V = B by tr_(B/Q)(x beta y star), with beta star = -beta, and
defines the right-action adjoint by beta x star beta inverse. It gives
the combined adjoint identity for B and B opposite. Section I.6,
printed p.45 (PDF p.53), specifies the reduced-then-center trace
convention, implemented here through `RationalTrace`.

The algebraic proofs above apply without requiring the original
involution to be positive. The source additionally chooses positivity,
local invariants and archimedean signatures for its PEL construction.
This module constructs the form and its adjoint from an actual skew
unit; it does not choose such a unit or assert that its beta-conjugated
involution has the Harris signatures. It also does not identify the
bilinear similitudes with an algebraic group, extend the pairing to
adeles, or construct polarizations, Tate pairings or moduli spaces.
