# Normalized regular orbital profiles on a division algebra

`RegularDivisionOrbitalProfileStatement.{u}` concerns a finite-dimensional central
division algebra `D` over a characteristic-zero nonarchimedean local field `F`, both
in universe `u`. It gives `D` its `F`-module topology and uses the Borel sigma-algebra
on the unit group. For every left Haar measure on `Dˣ` it asserts the existence of
compatible quotient measures on the regular centralizer coset spaces. The
centralizer Haar measures give the largest compact open subgroups mass one.

The parameter map is `divisionCoefficients F D`, restricted to the units with
separable reduced characteristic polynomial. `RegularOrbitalProfileData` asserts
that this locus is open and that the parameter map is continuous, open and
conjugation invariant. The orbit integrands of regular-supported Schwartz–Bruhat
functions are integrable. Their normalized orbital integrals are locally constant
on the regular locus and equal at units with the same parameters. It follows by
`RegularOrbitalProfileData.exists_profile` that these integrals descend to a
Schwartz–Bruhat function on the coefficient space, extended by zero outside the
regular parameter image.

The formulation isolates the division-algebra input of the regular-support
transfer in Badulescu (2002), §5, printed p. 733, and §6, printed pp. 745–746,
`badulescu-2002-jl-char-p` (registered folder SHA-256
`dc96cc7848166e83a1f23478a1e341928ea8565bc9b649ffe84e452f3a205028`, published PDF
SHA-256 `638e7134bb13c9c718ee7e5c2c9f06634637598c6ba8cd465345baf1234ed370`). The
source describes local constancy on regular conjugacy classes and normalizes
by the volume of the centralizer modulo the center. The proposition uses
compatible Haar quotients and mass one on the largest compact subgroup. The
normalization is natural under topological group isomorphisms, as in the
measure transport used by the transfer. The topology, integrability and
coefficient descent clauses express the regular profile construction in
these coordinates. This module states the proposition.
