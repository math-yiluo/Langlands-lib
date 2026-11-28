# Finite Weyl enumerations and estimates on the truncation ray

`WavePacketWeylEnumerationStatement` uses the actual Weyl conjugations
between two parabolics, with a root presentation of the first,
a rational Levi of the second and retractions onto both Levis.
It supplies a finite enumeration of their Weyl parameter maps,
with a conjugation representative for every enumerated map.

If the Weyl parameter set is nonempty, `finite_weylParameterSet`
chooses a reverse Weyl conjugation. Composition with its linear
equivalence injects the parameter set into the finite self-Weyl
parameter set of the first parabolic. `exists_weylParameterEnumeration`
then identifies the subtype with a finite ordinal and chooses its
representatives. The empty parameter set gives an empty enumeration.

`zero_isSquareIntegrableInducedForm` uses the zero automorphic
function and the vanishing square norm to give the zero padding
vector of each inducing space. `tendsto_truncationRayError`
uses divergence of the natural-number parameter on the ray and
decay of \(e^{-\delta t}\) for \(\delta>0\).

The Weyl sets and inducing spaces are those of E. Lapid,
*On Arthur's asymptotic inner product formula of truncated Eisenstein
series*, Clay Math. Proc. 13 (2011), §2, pp. 310–312
(volume PDF pp. 319–321). The finite enumerations and exponential
limit are used for the compact-uniform estimate of Proposition 1,
formula (2), §3, p. 313 (volume PDF p. 322), in the wave-packet
pairing of §8, p. 328 (volume PDF p. 337).
