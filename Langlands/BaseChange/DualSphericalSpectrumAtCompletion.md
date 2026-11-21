# Spherical spectra of dual components at actual completions

`DualSphericalSpectrumAtCompletionStatement` gives the inverse Satake multiset
for the actual contragredient component at a finite place outside the original
cuspidal presentation's exceptional set. It uses irreducibility and
admissibility of both actual finite components and the supplied global
contragredient relation. The place may belong to the dual presentation's
exceptional set.

The local helper applies to an actual object with a supplied spherical Hecke
spectrum and an object equivalent to its smooth contragredient.

Compact-open fixed-vector duality supplies a dual spherical vector pairing
nontrivially with a spherical vector of the original component. The standard
Hecke operators on the two fixed spaces have adjoint scalars for this pairing.
The adjoint scalar identity gives the inverse multiset. Local compatibility
identifies the actual contragredient component with the smooth dual, so the
calculation applies to the dual Euler factors of the global pair equations.

This is internal support for the comparison of the dual Euler factors in
Arthur–Clozel, Chapter 1, proof of Proposition 6.9(ii), completed equations
(6.15) and (6.16), printed p. 70 (PDF p. 84).
