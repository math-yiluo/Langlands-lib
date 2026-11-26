# The cuspidal cover of simple types over a fixed character

Let \(F\) be a nonarchimedean local field, \(V\) an \(F\)-vector space of
finite dimension \(N\ge 1\), and \(\psi_F\) an `IsBKAdditiveCharacter`.
Let \(\theta\) be a simple character for a simple stratum
\([\mathfrak A,n,0,\beta]\) on a principal order. Write \(E=F[\beta]\), let
\(k_E\) be its residue field and let \(f\) be the common dimension of the
layers of the centralizer lattice chain over \(k_E\). The Lean expression
for \(f\) uses the layer at index zero.

`SimpleTypesOverCharacterCoverStatement` asserts the existence of a map
\(\Lambda\) from the irreducible cuspidal representations of
\(\mathrm{GL}_f(k_E)\) to representations of \(J(\beta,\mathfrak A)\).
Every value is a simple type over \((\mathfrak A,\beta,\theta)\).
Equivalent cuspidal representations have equivalent images, and every
simple type over \((\mathfrak A,\beta,\theta)\) is equivalent to some
image. The domain, map values and types covered by the map each have an
independent carrier universe. The equivalences are equivariant linear
equivalences, including across universes.

This is the surjective half of BK94 (3.6) on equivalence classes. The
construction on printed p. 124 uses a Heisenberg representation over
\(\theta\), a \(\beta\)-extension and the inflation of a cuspidal tensor
power. The choices needed for this construction belong inside the
existence assertion. The injectivity in the full bijection uses the
proof of BK93 (5.7.1), as explained before (3.6).

## Source

Bushnell–Kutzko, *Simple types in GL(N): computing conjugacy classes*
(1994), (3.1), printed p. 123, (3.2), (3.3) and the paragraph defining a
simple type over \(\theta\), printed p. 124, and (3.6), printed p. 125
(volume PDF pp. 136–138).
Literature ID `bushnell-kutzko-1994-simple-types-conjugacy-classes`,
SHA-256 `fd2077476192d9db15188feea9ff73774fe96296a2a31412d612f2081581efaa`.
