# Compatible normalized Haar on nested radicals

For \(P_I \subseteq P_Q\), let \(N_I\) and \(N_Q\) be their unipotent
radicals, and write \(N_I = N_Q \rtimes W\) for the splitting through the
Levi of \(P_Q\). `NestedRadicalHaarStatement` uses the actual adelic
coordinates of this splitting. It says that multiplication
\((n,w) \mapsto nw\) takes the product Haar measure on
\(N_Q(\mathbb A)\times W(\mathbb A)\) to Haar measure on \(N_I(\mathbb A)\)
when each Haar measure is normalized by the mass of its own principal quotient.

For a closed adelic subgroup the quotient mass of its unscaled Haar measure is
the mass of a fundamental domain. This identifies
`AdelicSubgroupPoints.normalizedHaarMeasure` with
`LeftCosetSpace.Semidirect.latticeNormalizedHaar`. Compactness of the
principal quotient makes the quotient mass finite and positive, so the
normalized measure is Haar and the fundamental domain has mass one.

`NestedRadicalCoordinates` identifies the principal lattice of the normal
factor with the inverse image of the full lattice. Its section and projection
preserve the principal lattices. Compactness of the normal and complementary
principal quotients gives both finite-volume hypotheses of
`LeftCosetSpace.Semidirect.semidirectNormalizedHaar`. That theorem gives the
exact pushforward, and the multiplication homeomorphism gives measurability.

This is the compatibility of the radical factors in successive Iwasawa
integrations used in the passage from (7.23) to (7.26).

Source. P. Delorme, *On the spectral theorem of Langlands*, Advances in
Mathematics 426 (2023), 109107, §7, journal pp. 28–30, (7.23) and (7.26).
