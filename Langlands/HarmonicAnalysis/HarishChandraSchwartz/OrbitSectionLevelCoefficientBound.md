# Uniform coefficient bounds on a fixed section level

This is an internal derived strengthening of the existing conditional VI.2.2
bound. It makes the dependence on the section uniform on each fixed input
level. It does not discharge the lower coefficient Xi bound, establish
all-real Schwartz decay, or prove the source-normalized VI.3.1 target.

`exists_levelFamily_bound_of_basis` applies to a family of linear functionals
`a z g` on the actual compact coefficient picture. Suppose every vector in
the `H × H` fixed coefficient subspace has a bound `C_v * Xi(g)`, uniform in
the parameter `z` and the group point `g`. A finite basis of this subspace
then gives a finite collection of ambient linear functionals and one
nonnegative constant bounding every section of `OrbitSectionLevel H` by the
finite supremum of the corresponding input seminorms with empty derivative
list, times `Xi(g)`. The constant and finite set are independent of the
section, parameter and group point.

The proof extends each basis coordinate functional to the full compact
picture with `LinearMap.exists_extend`. The fixed-valued compact restriction
of a level section expands in the chosen basis. Its coordinate amplitudes
are bounded by the published input derivative seminorms of order zero.
The triangle inequality, the vectorwise bounds for the basis vectors, and
the sum of their constants give the asserted estimate. No topology comparison
or new section topology is introduced.

`unitaryOrbitCompactCoefficient` is the actual coefficient functional at a
unitary parameter, after inverse transport from the common compact picture.
Its restriction formula recovers the original coherent orbit coefficient.
`exists_levelOrbitCoefficient_bound` applies the preceding finite-basis
argument to these actual functionals. It uses the published theorem
`finiteDimensional_orbitSectionFixedCoefficients`, which derives finiteness
from compactness, admissibility and compact-open cofinality of the Levi. The
published `norm_twist_coefficientMap_le_xi` gives the required vectorwise
uniform bound, under its existing hypotheses. Finally the surjective actual
orbit map passes the estimate from torus parameters to every orbit class.

`orbitSectionLevelCoefficientControl` chooses the resulting nonnegative
constant times finite supremum as a seminorm on the input level. The theorem
`norm_levelOrbitCoefficient_le_control` bounds every actual orbit coefficient
by this seminorm times Xi. The continuity proof uses the existing level
seminorm topology and continuity of finite suprema and constant multiples.

`orbitSectionLevelWavePacketControl` multiplies this coefficient control by
`B * orbitMeasure.real univ`. For a weight with norm at most `B`, a finite
character measure and the existing finite self-twist stabilizer,
`norm_levelOrbitWavePacket_le_control` bounds the literal wave packet by this
new seminorm times Xi, uniformly for all sections at the input level. The
proof bounds the integrand pointwise and uses the norm bound for its Bochner
integral. The total orbit mass is retained exactly; no probability scale is
substituted. The packet control is again a continuous input seminorm.
No integrability or linearity assertion is inferred solely from this bound.

The analytic premises are explicitly those of the Library's conditional
VI.2.2 argument: unimodular radical modulus, the displayed Levi data and
Iwasawa pairs, the minimal modulus on the compact subgroup, and the
coefficient Xi bound for the inducing representation. Square integrability
is used to form the actual orbit; its implication of the lower Xi bound is
not proved in this module. These remain internal premises to discharge when
applying this construction to the exact source-normalized task.

The registered original is Waldspurger 2003, source ID
`waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
Lemma VI.2.2 and its proof, printed pp.298-299 (PDF pp.64-65), bound the
unitary-twist coefficients through finite-dimensional coefficient spaces,
Corollary III.1.2 and Lemma II.1.6. The new fixed-input-level control is an
internal finite-basis consequence of the published Library version of that
argument. VI.3, printed p.302 (PDF p.68), defines the orbit wave-packet
integral. Higher derivatives, central Fourier decay, weak lower-Levi terms
and positive-part decay remain necessary for the full VI.3.1 estimates.
