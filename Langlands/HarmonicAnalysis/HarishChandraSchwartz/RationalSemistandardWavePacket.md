# Actual semistandard coefficients and source wave packets

This derived construction supports the weighted synthesis of Waldspurger's
invariant spectral families.
Its principal declaration is
`Langlands.HarishChandraSchwartz.RationalSemistandard.SourcePacket.rawWavePacketLinear`.
It constructs the actual one-orbit source integral and proves its pointwise
integrability and complex linearity. It does not construct global
weighted synthesis (`RationalSemistandardWeightedSynthesis`) or a
Schwartz-valued lift.

The source is J.-L. Waldspurger (2003), *La formule de Plancherel pour les
groupes p-adiques*, registered as `waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
VI.1, printed pages 295–296 (PDF pages 61–62), supplies the coefficient
fibers and coefficient function. VI.3, printed page 302 (PDF page 68),
defines the integral of the actual density times that coefficient over the
unitary orbit. The source character scale is I.1, printed page 239 (PDF
page 5), and the actual density is V.2, printed page 292 (PDF page 58).
The elementary proof route below uses the published compact-picture orbit
coefficient, source measures and density. It does not reproduce the
substantive standard-Levi VI.3.1 Schwartz estimates.

The field has arbitrary characteristic and independent universe `u`;
representation carriers have independent universe `uV`. The ambient group
scheme is affine, locally of finite type and connected reductive. The
intrinsic index `t`, actual `LeviModel model`, literal Levi `M`, and
`CompactData d` retain their published meanings and canonical point
topologies. No ambient splitness, quasi-splitness or representation-carrier
topology is added. Rank zero is included. An actual
`CocharacterPresentation hG t` identifies the whole all-test triple with
a dynamic triple; existence from the dynamic-coverage target remains
conditional in the preceding adapter. The compact-picture
projection continuity and actual Iwasawa factorization remain in `d`.

`RationalSemistandard.isClosed_levi_of_model` follows from the model's actual closed
inclusion. `levi_modularCharacter` transports the published connected
reductive rational-point unimodularity through `model.pointHomeomorph`.
`radical_isUnimodular` specializes the actual dynamic-radical theorem by
eliminating the presentation's triple equality. The generic semidirect
modular-character theorem then proves `parabolic_modularCharacter` using
these two factors and `d.projection_continuous`. Ambient unimodularity is
the published `rationalReductiveUnimodularity` theorem. These properties
are proved; no modular-character conclusion is taken as data.

In namespace `RationalSemistandard.SourcePacket`, `coefficientMap` is the
existing `unitaryOrbitCoefficientMap` at these exact subgroups and compact
data, on precisely `smoothOrbitSections model d pi`. It is complex linear.
The displayed central subgroup `C`, quotient Haar `mu`, and actual
square-integrability proof are the original ones used by the orbit.
`coefficientMap_representative` retains every actual inducing
representative. It is the published coherence and transport theorem, not
an equality restricted to one chosen inducing object.
`continuous_coefficient` specializes the published finite-torus smoothness
and orbit-quotient continuity theorem using the model's proved Laurent
coordinates.

`coefficientMap_leviNormalization` identifies the entire coefficient
function with the positive-Levi source coefficient after the existing
actual `productInducedCoefficientLeviEquiv`. Its proof applies
`CompactInduction.leviCoefficientMap_compare`, with the radical
unimodularity just proved. Thus the original compact Haar probability
normalization and actual inducing tensor comparison are preserved. No
free coefficient map or scalar is introduced.

The source-normalized section takes an actual affine split-component
scheme and morphism `a`, proof `ha`, and the actual finite-index premise
`hindex : (RenardCartan.splitValuationImage a).FiniteIndex`. Its central
subgroup is exactly `model.splitCenter a`; the literal quotient has the
displayed Borel measurable space and Haar `mu`. Both normality instances
are explicit as required by the existing quotient APIs and follow from
centrality. The main inducing representation stays on the literal Levi.

The orbit measure `eta` is exactly
`SourceMeasure.normalizedOrbitMeasure`, the pushforward of the original
source-normalized rational orbit measure. Its total mass retains the
restriction-kernel cardinality divided by the unramified self-twist
cardinality. The valuation-image finite-index premise remains an
outstanding structural obligation, not a new permanent external input.
The finite-measure instance is inherited from the source-measure adapter.

The weight `W` is exactly `SourceDensity.orbitPlancherelWeight`, with every
conditional scalar input displayed: relative-root reflection and central-
split-torus character statements, scalar compact `Ks` with both parabolic
factorizations, forward and reverse continuation data, nonempty open
convergence loci inside the full domains, a nonempty open generic
irreducibility locus, and full-unitary regularity of the inverse canonical
composition scalar. These obligations are not discharged here.
`Ks` is independent of the coefficient compact in `d`. No irreducibility
assumption on all tempered parabolic induction is added.

`sourceOrbit_compactSpace` transports compactness of the finite product of
circles through the model's actual character coordinates and then through
the actual character/self-twist quotient. `integrable_wavePacketIntegrand`
multiplies the proved continuous density and coefficient on this compact
orbit, bundles the scalar function as bounded continuous, and uses its
integrability for the actual finite source measure. This proves pointwise
Bochner integrability for every smooth section and ambient group point;
it does not infer a Schwartz bound from compactness.

`rawWavePacket` is the exact actual integral

```text
f_v(g) = integral over omega of W(omega) * coefficientMap(v)(omega)(g) d eta.
```

`rawWavePacket_eq_literalMeasure` identifies this with the integral for
the existing `discreteSeriesOrbitMeasure` and the fixed actual I.1
`unitaryCharacterHaar`. Its displayed finite self-twist instance is
supplied by `SourceMeasure.finite_literalDiscreteSeriesStabilizer`, so no
independent self-twist finiteness hypothesis is needed mathematically.
The measure comparison is equality, with no replacement by probability
measure.

`rawWavePacket_smul` moves a constant through the integral and uses
coefficient linearity. `rawWavePacket_add` applies integral additivity to
the two proved integrable actual integrands. They bundle to
`rawWavePacketLinear`, a complex-linear map into actual complex-valued
functions on `G(F)`. No integrability or linearity conclusion is assumed.

The actual standard-specialization, model and representative-change
comparisons of the complete source packet, source formal-degree transport,
Schwartz membership and continuous lift, weighted global sum, invariant
restriction and VI.3.2 factorization are additional constructions and
targets, not in this module. The standard VI.3.1 estimates and the
source-topology comparison are separate. This file proves no global
form, VII.2.5 isometry or VIII Fourier-support finiteness/inversion.
