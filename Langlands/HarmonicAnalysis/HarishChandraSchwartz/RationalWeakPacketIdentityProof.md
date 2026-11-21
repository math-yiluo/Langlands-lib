# From the weighted weak expansion to the packet identity

`WeightedPacketIdentityReductionStatement` is the implication from the
published `WeightedWeakExpansionStatement` to the published
`WeightedPacketIdentityStatement`. The premise supplies the expansion at
every orbit point and every lower Levi point under the original hypotheses on
the compacts, the Weyl lifts and the two density packages. The implication
retains independent universes for the field and representation carrier.

`weightedPacketIdentity_of_weightedWeakExpansion` takes the same weighted
rational extensions and lower sections from the pointwise witnesses. The
source integral uses `discreteSeriesOrbitMeasure` with
`standardLeviUnitaryUnramifiedCharacterHaar`. For each Weyl index, the product
of the lower density and the lower section coefficient is continuous by
`DynamicInducedOrbit.continuous_orbitPlancherelWeight` and
`DynamicInducedOrbit.continuous_inducedOrbitCoefficientMap`. The published
`continuous_lowerOrbitMap` gives continuity of its pullback. Compactness of
the source orbit follows from `leviRationalUnitaryCoordinates` and
`compactSpace_discreteSeriesOrbit`. The measure is finite by
`isFiniteMeasure_standardLeviOrbitMeasure`. These facts give Bochner
integrability of each pullback. The proof applies `integral_congr_ae` to the
pointwise equality and interchanges the finite sum and integral by
`integral_finsetSum`.

`discreteSeriesOrbitCharacterEquiv` gives the conjugation homeomorphism of
the two discrete-series orbits. Its agreement with `lowerOrbitMap` follows
by evaluating both maps on the surjective unitary character parameterization
using `discreteSeriesOrbitCharacterEquiv_orbitMap` and
`lowerOrbitMap_orbitMap`. The map theorem
`map_discreteSeriesOrbitMeasure_characterEquiv` transports the source orbit
measure to the orbit measure built from `lowerCharacterMeasure`, the image
of the source character Haar measure under character conjugation. The theorem
uses equality of the self-twist stabilizer cardinalities, so the factors
from the two finite quotients agree. `MeasurePreserving.integral_comp`
now computes the pulled-back integral as the lower Bochner integral in
`DynamicInducedOrbit.inducedOrbitWavePacket`.

This derived implication formalizes the integration step of J.-L. Waldspurger,
*La formule de Plancherel pour les groupes p-adiques (d’après Harish-Chandra)*,
J. Inst. Math. Jussieu 2 (2003), 235–333, VI.3.1 on printed pp. 303–304 and
the normalization in I.1 on printed pp. 240–241. The registered source is
`waldspurger-2003-plancherel`.
