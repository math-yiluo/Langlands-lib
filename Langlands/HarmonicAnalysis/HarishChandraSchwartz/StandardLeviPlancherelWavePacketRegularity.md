# Elementary source-normalized packet regularity

Worker 658, Task 7423. This internal construction supplies elementary regularity
and algebraic synthesis for the published
`StandardLeviPlancherelWavePacketSourceNormalizedStatement`. It does not establish
that full analytic target.

The source is J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques
(d’après Harish-Chandra)* (2003), registered source `waldspurger-2003-plancherel`.
The packet integral and Proposition VI.3.1 occur on printed p.302 (PDF p.68).
These elementary prerequisites use a compactness argument rather than the full
chamber induction on pp.302–305.

At each fixed actual rational point, `continuous_standardLeviPlancherelWavePacket_integrand`
combines the published coefficient continuity
`Langlands.Plancherel.continuous_unitaryOrbitCoefficient` with
`Langlands.Plancherel.continuous_standardLeviPlancherelWeight`.
The canonical Laurent circle coordinates and the actual standard-parabolic
Iwasawa data specialize the coefficient theorem. No coefficient Xi bound is used.

`integrable_standardLeviPlancherelWavePacket_integrand` obtains compactness of the
unitary character group from `leviRationalUnitaryCoordinates`, and compactness of
the orbit from `compactSpace_discreteSeriesOrbit`. It installs the existing
finite self-twist result under the displayed `hindex` and reuses
`isFiniteMeasure_standardLeviOrbitMeasure`. A continuous scalar function on this
compact orbit has compact support and is integrable for the finite orbit measure.
The integral measure is exactly the source-normalized one in the target, with no
probability renormalization.

`exists_standardLeviPlancherelWavePacket_biInvariant` specializes the published
`exists_rationalInducedOrbitWavePacket_biInvariant` to the actual weight and
measure. It produces a compact open subgroup inside K for each smooth section.

`standardLeviPlancherelWavePacketLinear` packages the literal packet as a complex
linear map from `rationalInducedSmoothOrbitSections` to complex-valued functions
on the actual group. Additivity uses the compact-orbit integrability proved above,
`integral_add`, and linearity of the orbit coefficient map. Scalar compatibility
reuses `rationalInducedOrbitWavePacket_smul`. The accompanying `_apply` lemma is
reflexivity. This construction needs neither a coefficient Xi bound nor an
Iwasawa hypothesis for the compact subgroup inside the Levi. Its codomain is the
space of functions, with no asserted continuity into the Schwartz topology.

This is a derived construction from the already published packet, coefficient
and measure definitions, with their defining laws proved in the same module.
The cited source motivates the integral and its intended analytic role; the
compactness argument and the algebraic packaging are internal prerequisites.

Field and representation-carrier universes remain independent. The literal
standard-Levi representation, central split component, quotient Haar, actual
conditional weight, and distinct Ks and K are unchanged. These theorems introduce
no additional analytic premises. They prove pointwise integrability and smoothness
of the packet. Full all-real Schwartz seminorm bounds and continuous synthesis
into `RationalSchwartzSpace` are still open.
