# The conjugate-Levi wave-packet pairing

Waldspurger VII.2.2(ii) gives the pairing of smooth wave packets on
semistandard parabolics \(P=MU\) and \(P'=M'U'\) with conjugate Levis.
The full indices \(t=(P,\mathcal O)\) and \(t'=(P',\mathcal O')\) retain
the unitary unramified discrete-series orbit of each literal rational
Levi. The sections \(v\) and \(v'\) are smooth coherent sections over
every actual inducing representative.

`ConjugatePairingStatement` is the proposition for that case. Its
conclusion is
\[
\int_G\overline{f_{v'}(g)} f_v(g)\,dg =
\gamma(G\mid M)c(G\mid M)^2
\sum_{\substack{s\in W(M'\mid G\mid M)\\s\mathcal O=\mathcal O'}}
\int_{\mathcal O}\mu(\omega)
\langle v'_{s\omega},\,{}^\circ c_{P'\mid P}(s,\omega)v_\omega\rangle
\,d\omega.
\]
The pairing is conjugate linear in its first slot. `LevisConjugate`
asserts equality of the literal Levi image under conjugation by a
rational point with the target literal Levi. `orbitWeylPairingSum`
sums over the filtered left target-Levi quotient. The equivalence
`orbitWeylTransportersEquiv` identifies this carrier with the filtered
source transporter quotient in V.1. Each class contributes once.
The proof of `orbitWeylPairingSum_of_isEmpty` gives zero when no
class carries the two specified orbits onto one another, including
when the Levis are conjugate.

## Actual orbit integrals

`orbitWeylPointMap` uses the same chosen compact lift as
`normalizedWeylSection`. It conjugates the actual inducing class
and uses `compactLift_targetOrbit` to regard that class as a point of
\(\mathcal O'\). `orbitWeylPointMap_representative` projects through the
two subtype coordinates and applies the equality of inducing pullbacks
from `compactLift_conjugateRepresentative_val`. The resulting
representative is the one used by the coefficient comparison.
`orbitWeylPairingIntegrand_representative` evaluates the scalar
integrand in that representative by `SourceForm.pairing_representative`.
Together with `normalizedWeylSection_realizes`, this gives the
inverse-formal-degree tensor pairing with the actual normalized
comparison at every such representative. Coherence retains every
inducing equivalence.

`orbitWeylPairingIntegrand` multiplies this target-fiber pairing by the
actual **source** `GlobalForm.componentDensity`. Its integral uses the
source `SourceMeasure.normalizedOrbitMeasure`, with the I.1 character
scale and reciprocal finite self-twist stabilizer cardinality.
`orbitWeylPointMap_measurePreserving` takes the orbit classes of the two
chosen bases and uses `compactLift_targetOrbit` to identify the conjugate
source base class with the target base class in the unitary-twist quotient.
This defines `SourceMeasure.orbitConjugationRecentered` for the compact
lift and the two chosen bases. The homeomorphism is measurable and agrees
with `orbitWeylPointMap` on underlying discrete-series classes by
`SourceMeasure.orbitConjugationRecentered_val`.
`SourceMeasure.normalizedOrbitMeasure_map_conjugationRecentered` gives
the equality of the transported and target measures.

`OrbitWeylDensityTransportStatement` specifies pointwise equality of the
source density with the target density pulled back along this map.
`orbitWeylPairing_changeVariables` uses the published
`SourceForm.integrable_pairing` for the target orbit, pulls that integrable
function back along the measure-preserving map, and replaces the
pulled-back density by the source density. The integral identity follows
from `MeasureTheory.integral_map`. This proves
`OrbitWeylPairingIntegrabilityStatement` under the density transport
premise and identifies each term with the actual target
`GlobalForm.componentForm`.

## Ambient pairing and proof inputs

The ambient Haar gives the common special compact \(K\) mass one.
`SourceCompactCompatibility` identifies the compact in both coefficient
pictures and the scalar data. `IsSourceCompactAt` and
`SourceLeviQuotientHaar` retain the source apartment condition and the
mass-one image of \(K\cap M\) and \(K\cap M'\) in the respective
split-central quotients. `LeviNormalizationMatches` identifies the
comparison quotient Haar with the source normalization.
`OrbitWeylDescentStatement` supplies existence, realization and
independence of the actual comparison.

`WavePacketPairing.integrable_pairing` proves ambient scalar
integrability with the displayed square-integrable weight and
`ComponentSchwartzMembershipStatement`. To apply formula (1),
`packet_pairing_eq_componentForm` takes the test packet at \(t'\)
and the `schwartzPacket` at \(t\). Its VI.2.2 double-integrability
input is `OrbitProductIntegrabilityStatement` at \(t'\), and its
density input is `GlobalForm.DensityNonnegative`. It also needs the
Schwartz packet's `rationalSemistandardFourierFamily` component at
\(t'\) to be a smooth coherent section.
`RationalSemistandardFourierFamilySmoothnessStatement` gives that
membership under the component's `RationalSemistandardFourierAnalyticInputs`.
The theorem applies Fubini and `orbitCoefficient_pairing`, which
uses the actual VII.1.1(ii) coefficient pairing.

The source then uses VII.1.4 to compare the Fourier components at
the two parabolics and VII.2.1 to compute the same-Levi component.
These are the full Fourier covariance obligation of the Fourier
product family (VII.1.4) and
`FourierWeylSumStatement`, respectively. With the component
computed, `orbitWeylPairing_changeVariables` identifies its
target-orbit pairing terms with the displayed source-orbit
integrals. `ConjugatePairingStatement` gives the resulting ambient
pairing equality as the target.

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques
(d’après Harish-Chandra)*, J. Inst. Math. Jussieu 2 (2003), 235–333.
V.1 and V.3, printed pp. 288 and 295–296 / PDF pp. 54 and 61–62,
give the Weyl quotient and comparisons. VI.2.2 and VII.1.1(ii), printed
pp. 298–299 and 314 / PDF pp. 64–65 and 80, give the pairing inputs.
VII.1.4 and VII.2.1–VII.2.2, printed pp. 317–319 / PDF pp. 83–85,
give the covariance, Fourier computation, and conjugate-Levi
pairing. [Registered source](https://doi.org/10.1017/S1474748003000082)
