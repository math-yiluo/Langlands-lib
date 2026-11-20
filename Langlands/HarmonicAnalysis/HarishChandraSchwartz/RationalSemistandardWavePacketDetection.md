# Semistandard packet detection and Fourier vanishing

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques
(d'après Harish-Chandra)*, J. Inst. Math. Jussieu 2 (2003), 235–333.
The registered source is `waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
Corollary VII.2.3 and formula (1) of the proof of VII.2.2 are on printed
p. 319 (PDF p. 85), VII.1.1(ii) is on printed p. 314 (PDF p. 80), and
VI.2.2 is on printed p. 298 (PDF p. 64).
[Original article](https://doi.org/10.1017/S1474748003000082)

The setting is an arbitrary nonarchimedean local field with finite residue
field and an affine, locally finite type connected reductive group scheme.
The topology is the canonical rational-point topology. The field and
complex `SmoothRep` carrier universes are independent. This includes
positive characteristic, nonsplit and non-quasisplit groups, and rank zero.
The source and target parabolics, their literal Levis, the orbits and the
coherent smooth sections come from the intrinsic semistandard family.

`PointwiseVanishingStatement` asserts VII.2.3 for every source packet
`f_psi` from `(P,O)` and every semistandard `P'` whose Levi is nonconjugate
to that of `P` in `G(F)`. The conclusion is `fourierAt P' A f_psi = 0`
in the actual Fourier coefficient fiber at each square-integrable
irreducible admissible representative `A` of the target Levi. The
equivalent `ComponentVanishingStatement` gives zero in the full Fourier
product at every `(P',O')` of that Levi. Evaluation on all inducing
representatives implements the equivalence. Each discrete-series object
is used as a member representative in its actual orbit, so its
coefficient fiber is the very one computed by the pointwise transform.
The imported full product already respects inducing equivalences,
including self-twists.

Both targets take `SourceCompactCompatibility` and the preceding
`ComponentSchwartzMembershipStatement` to form the actual Schwartz packet.
Its evaluation is the density-weighted coefficient integral.
`RationalDynamicSource.ambientHaar` gives ambient Haar mass one on the
source compact `K`, and ambient reductivity gives its right invariance.
The orbit integral uses `SourceMeasure.normalizedOrbitMeasure` with the I.1
character scale and the reciprocal cardinality of the unramified self-twist
stabilizer. The split valuation image has finite index as in the packet
data. `OrbitPacketData` retains inverse scalar regularity on the entire
unitary locus. The Fourier construction retains the ambient square-integrable
weight, modular normalization, and tempered coefficient input at every
actual square-integrable inducing object.

| Declaration | Result and immediate dependencies |
| --- | --- |
| `fourierAt`, `fourierComponent_apply` | The actual `rationalSemistandardInducedFourierTransform` and its evaluation in `rationalSemistandardFourierFamily`. |
| `fourierComponents_eq_zero_iff_forall_fourierAt_eq_zero` | The pointwise and product zero conditions agree by `orbitRepresentativeMember`, the evaluation formula and function extensionality. |
| `finite_componentNormKernelQuotient` | The private adapter transports `finite_rationalCentralQuotient` through `LeviModel.pointHomeomorph`. That identification carries all rational-character norm kernels and the split-center image onto their literal Levi versions. |
| `componentForm_self_eq_zero_iff` | The core of `PlancherelOrbitWavePacketOrthogonality`, `unitaryOrbitWeightedProductPairing_self_eq_zero_iff_of_dense`, applies to the real part of the actual `GlobalForm.componentDensity`, the source orbit Haar and the actual inverse-formal-degree pairing. Continuity follows from scalar inverse regularity and gives boundedness on the compact orbit. The premises are `GlobalForm.DensityNonnegative` and `GlobalForm.DensityPositiveDense`. They allow zeros of the density. |
| `OrbitProductIntegrabilityStatement` | The exact double integrability used for formula (1) of VII.2.2. It is the needed consequence of the uniform coefficient bound by a constant times the spherical function in VI.2.2, with the packet density and a Schwartz test. |
| `orbitCoefficient_pairing` | The VII.1.1(ii) pairing result `rationalSemistandardFourier_pairing`, evaluated at an actual representative. `SourcePacket.coefficientMap_representative` and `SourceForm.pairing_representative` give its descent to the orbit. |
| `packet_pairing_eq_componentForm` | Formula (1) with a Schwartz second argument. Fubini uses the preceding double integrability, nonnegativity makes the conjugated density equal to the density, and the coefficient pairing is conjugate linear in the first argument. |
| `component_eq_zero_iff_forall_pairing_eq_zero` | Pairing against every smooth source packet detects a smooth Fourier component. In the reverse direction choose the actual Fourier component as the smooth test and use definiteness of its component form. |
| `PointwiseVanishingStatement`, `ComponentVanishingStatement`, `pointwiseVanishing_iff_componentVanishing` | The two VII.2.3 targets and their proved equivalence. |
| `componentVanishing_of_nonconjugatePairing` | Conditional deduction of VII.2.3 from `NonconjugatePairingStatement`, actual density nonnegativity and dense positivity, double integrability and smooth Fourier membership. |

The smooth Fourier membership in the last adapter is the conclusion of
`RationalSemistandardFourierFamilySmoothnessStatement` after supplying
`RationalSemistandardFourierAnalyticInputs` at each component. The deduction
implements Waldspurger's all-smooth-test argument with the existing
actual-density detection theorem. VII.2.2(i) is a substantive premise of
that deduction. The two VII.2.3 propositions state the vanishing directly,
with proof obligations following from the preceding inputs.
