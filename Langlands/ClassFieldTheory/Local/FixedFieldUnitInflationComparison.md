# Continuous inflation from finite fixed fields

Let \(L/K\) be a Galois extension, \(H\) an open normal subgroup
of its Krull Galois group, and \(E=L^H\).
`fixedFieldContinuousUnitInflation` is continuous inflation from
\(H^q(\operatorname{Gal}(E/K), E^\times)\) to
\(H^q_{\mathrm{cont}}(\operatorname{Gal}(L/K), L^\times)\).
It uses restriction of automorphisms to \(E\) and the inclusion
of units \(E^\times \hookrightarrow L^\times\). All unit groups
have the discrete topology.

The finite quotient \(\operatorname{Gal}(L/K)/H\) identifies
with \(\operatorname{Gal}(E/K)\) by the same restriction, and its
fixed unit module identifies with the units of \(E\) by their
inclusion in \(L\). These two facts give the cochain comparison
for `finiteStageToContinuous_eq_mapIso`. Since \(E/K\) is finite,
the continuous-to-ordinary comparison for the source is an
isomorphism. The theorem
`continuousToOrdinary_comp_fixedFieldUnitInflation` identifies
continuous inflation with finite-quotient inflation after this
comparison. The identity holds in every cohomological degree.

This derived comparison implements the ordinary finite-stage
inflation into continuous cohomology used in Serre, *Local Fields*
(1979), Chapter X, §5, printed p. 159, and Chapter XII, §1,
Theorem 1, printed p. 181. Its proof specializes the Library's
cochain factorization theorem to the actual fixed-field group
and unit inclusions.
