# Étale cohomology finiteness for proper schemes

Michael Artin, SGA 4, Tome 3, Exposé XIV, Corollaire 1.2, printed p. 145
(PDF p. 148), gives finite ordinary étale cohomology in every degree for
constructible torsion abelian sheaves on a proper scheme over a separably
closed field. This proposition treats the finite locally constant case, in
the category of module sheaves with coefficients in a constant
commutative ring \(R\). Registered source ID
`sga4-1973-tome3-deligne-xvii-original-scan`, SHA-256
`702fa23766ccec841d31ce0f21dfaacff8d8d31d4153de386587a27a4c01107a`.

`Langlands.Cohomology.ProperEtaleFinitenessStatement` takes a proper
morphism \(X\to\operatorname{Spec}K\), where \(K\) is separably closed. For
each point of \(X\), `IsFiniteLocallyConstantEtaleSheaf` requires an
étale object whose image contains the point and on whose small étale
site the restriction is isomorphic to the constant sheaf of a finite
\(R\)-module. The ranges of these actual étale objects form a covering.
The conclusion is `Finite` on the carrier of each
`EtaleDerivedSections.cohomology X R q` evaluated on the sheaf.
There is no prime-to-characteristic condition.

The finite locally constant sheaf is constructible on the Noetherian
scheme \(X\) and its stalks are torsion. To pass from the abelian
statement of the corollary to \(R\)-modules, injective sheaves of
modules are flasque, and flasqueness is a property of the underlying
abelian sheaf. They therefore compute the same cohomology upon forgetting
scalars. This uses SGA 4, Exposé V, §4.1, §4.4 and §4.6, in the
original Tome 2 scan, printed pp. 29–30 (PDF pp. 31–32), registered ID
`sga4-1972-tome2-verdier-v-original-scan`, SHA-256
`7c5b8cef5a99d22785501eead8353641064f858c51ce361b00b310b2bcc46585`.
Finite coefficient modules may be nonfree.

For Harris's CM levels, the geometric base change of the projective
level is proper over the algebraic closure of the CM field. The
associated lattice sheaf modulo a coefficient power has an étale
trivializing cover with finite module values. This is the finiteness
input for `HarrisCMCohomologyFiniteStatement`, and corresponds to
Harris, *Galois properties of cohomological automorphic forms on GL(n)*
(1999), equation (4.9) and the proof of Proposition 4.10, printed
pp. 311–312. The registered Harris original is
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.
