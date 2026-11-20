# Proper orbit comparisons for VIII.2.2

`ProperOrbitSymmetryStatement` specifies the orbit comparisons that turn the
three induced character equalities in VIII.2.2 into identities of weighted
proper Fourier synthesis. Each comparison is made within the literal
semistandard parabolic. The index for a proper orbit therefore keeps the same
parabolic and the same unquotiented source coefficient.

`ProperOrbitCheckComparisonStatement` and `ProperOrbitConjComparisonStatement`
require permutations of the unitary orbits at each parabolic. An orbit
homeomorphism sends an actual inducing representative class to the class of
its smooth contragredient or conjugate complex representation. The matched
representatives have the same Schur degree for the prescribed Levi quotient
Haar. The homeomorphism preserves the source-normalized orbit measure and
identifies the two actual Plancherel densities in the packet integrals.

`ProperOrbitTwistComparisonStatement` uses the identity permutation of orbit
indices. Its homeomorphism acts within the orbit by the twist with the
restriction of the ambient character to the literal Levi. Preservation of
the actual packet density is the equality `μ(ω ⊗ χ) = μ(ω)` in VIII.2.2.
`ProperOrbitDensityRealStatement` gives the portion of V.2.1 reality that
allows conjugation to pass through the density-weighted proper integral.

`GlobalForm.OrbitPoint` and `GlobalForm.componentDensity` supply the orbit and
density of the actual synthesis. `componentOrbitMeasure` uses the
`SourceMeasure.normalizedOrbitMeasure` from the same packet integral.
`componentFormalDegree` uses the `representationFormalDegree` of VII.1.1(iii).
These propositions leave the geometric or analytic comparisons open.
The field and representation-carrier universes are independent, and the
statements use arbitrary-characteristic connected reductive groups.

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques
(d’après Harish-Chandra)*, Journal of the Institute of Mathematics of
Jussieu 2 (2003), I.1, V.2.1, VI.3, VII.1.1(iii), and VIII.2.2 on printed p. 322.
[DOI](https://doi.org/10.1017/S1474748003000082)
