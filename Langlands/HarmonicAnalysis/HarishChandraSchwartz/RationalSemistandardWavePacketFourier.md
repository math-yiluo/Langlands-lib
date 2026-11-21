# The Fourier Weyl sum for an actual semistandard wave packet

`FourierWeylSumStatement` gives the target of Waldspurger VII.2.1 for a
semistandard \(P=MU\), a unitary unramified discrete-series orbit
\(\mathcal O\) of \(M\), and a smooth coherent section \(v\) on that orbit.
For every actual square-integrable inducing object representing a
discrete-series class \(\omega'\) of \(M\), its conclusion is
\[
\widehat f_v(\omega',P)=
\gamma(G\mid M)c(G\mid M)^2
\sum_{\substack{s\in W(G\mid M)\\s^{-1}\omega'\in\mathcal O}}
{}^\circ c_{P\mid P}(s,s^{-1}\omega')v_{s^{-1}\omega'} .
\]
Both sides are in the coefficient fiber of the specified object.
`orbitRepresentativeMember` puts that object itself into the full
index \(t'=(P,[\omega'])\), where \([\omega']\) denotes its unitary
twist orbit. The left side evaluates `rationalSemistandardFourierFamily`
on that component and member. By definition, this evaluation applies
`rationalSemistandardInducedFourierTransform` at the specified inducing
object.

`schwartzPacket` uses `ComponentSchwartzMembershipStatement` to lift
`GlobalSynthesis.componentPacket` without changing its evaluation.
That packet integrates `SourceDensity.orbitPlancherelWeight` times the
actual induced coefficient against `SourceMeasure.normalizedOrbitMeasure`.
The measure retains the I.1 character Haar scale and the reciprocal
finite self-twist cardinality. `SourceCompactCompatibility` supplies
one special compact \(K\) for the coefficient pictures and every
`OrbitPacketData` scalar compact. Its ambient Haar measure gives \(K\)
mass one, and `sourceWeylScale` is the product of `SourceConstants.gammaReal`
and the square of `SourceConstants.cReal` for the source Levi and \(K\).

## Quotient and coefficient transports

`OrbitWeylTransporters` is the filtered left target-Levi Weyl quotient.
`orbitWeylTransportersEquiv` and `orbitWeylSum_eq_transporterSum` identify
it and its sum with the filtered inclusion quotient used in V.1.
`compactLift_transports_iff_inverse_constituent` applies the inverse
membership test to the orbit of \(\omega'\). Each qualifying class
contributes once, including separate classes with the same inverse
constituent. `fourierWeylSum_of_isEmpty` applies the empty quotient sum
identity and scalar multiplication by zero.

`sourceTorusCentralizer_le_levi` supplies the centralizer containment
from the actual `CocharacterPresentation`. The published
`finite_relativeWeylGroup` supplies finiteness under maximal splitness.
`compactWeylLift` uses `liftClass_surjective` and
`hasWeylRepresentatives_of_sourceCompact` to choose a representative in
\(K\). `compactLiftConjugatesLevi` gives the all-test Levi equality
and `compactLift_leviPullback` identifies the two literal inducing
pullbacks. `compactLift_base_orbit` and `compactLift_targetOrbit`
identify the orbit of the conjugated comparison base with \(t'\).
`compactLiftTargetBaseEquiv_apply` shows that the resulting change of
base evaluates at the same actual forward-conjugated object.

The comparison is conditional on `OrbitWeylDescentStatement`, the
instance of `WeylDescent.ClosedWeylDescentStatement` at the two indices.
Its `QuotientRealization` supplies the smooth equivalence
`normalizedWeylSection` with a `WeylSections.IsActualFamily`
certificate. At each inducing representative that certificate specifies
the actual regular V.3 comparison from standard intertwiners, reverse
dual inverse and rational-point translation, through `comparisonAtOne`.
`recenterTarget_compactLiftTargetBaseEquiv` proves that changing lifts
commutes with the intrinsic changes of orbit base.
`normalizedWeylSection_eq_of_realizes` applies quotient realization and
this recentering identity to any certified representative of the class.
`normalizedWeylSection_realizes` gives the value at its forward pullback,
and `normalizedWeylSection_hasActualFamily` gives the certificate at
the chosen lift.

For a specified target object, `compactLiftSourceRepresentative`
pulls it back into the source orbit using the inverse membership test.
`compactLiftInverseInducingEquiv` cancels inverse and forward
conjugation via `SmoothRep.pullbackSymmIso`.
`normalizedWeylSection_at_inverse` uses smooth section coherence
at that equivalence to give the V.3 value in the specified target
fiber via `productInducedCoefficientTransport`. This construction uses
coherence for every inducing equivalence, including self-twists.

## Normalization and preceding inputs

`SourceLeviQuotientHaar` gives the image of \(K\cap M\) in the split-central
quotient mass one. `LeviNormalizationMatches` asserts equality of the
actual split-center images and of the pushed-forward quotient measures
under the literal Levi homeomorphism. The theorem
`hasIntrinsicSourceNormalization_of_commonCompact` transports the
mass-one assertion along this homeomorphism and uses the apartment
condition `IsSourceCompactAt`. This gives the precise
`HasIntrinsicSourceNormalization` premise of comparison descent.
The Fourier family uses maximal splitness, genericity, the ambient
square-integrable weight, `ModularNormalization`, and the tempered
coefficient bound on the actual normalized inductions. The geometric
scalar inputs in `OrbitPacketData` are
`RelativeRootReflectionExistenceStatement` and
`CentralSplitTorusCharacterStatement`. Its remaining scalar inputs
include both parabolic factorizations, forward and reverse continuation
on nonempty open convergence domains, generic irreducibility on its
specified nonempty open domain, and full-unitary regularity of the
inverse canonical scalar. The split valuation image has the displayed
finite-index premise. The two universes of the field and the inducing
carriers are independent.

The following declarations are preceding inputs to the source proof
of the equality in `FourierWeylSumStatement`.

- `rationalSourceNormalizedOrbitPacketFourier` proves the \(M=G\)
  calculation under `RationalSourceNormalizedOrbitPacketFourierStatement`.
  Its central-mass adapter uses maximal compactness and the I.1
  normalization on \(A_G\cap K\) to set the factor
  \(\mu_A(A_G\cap G^1)\) in `coefficientFourierTransform_rationalOrbitWavePacket`
  equal to one. The theorem retains the compatible quotient
  disintegration and its measure equality, continuity of the orbit
  coefficients, integrability of packet translates on the center,
  Schwartz membership, the \(L^2\) weights and their inversion laws,
  and the target tempered coefficient bound.
- `WeakExpansion.WeightedWeakExpansionStatement` and
  `WeakExpansion.WeightedPacketIdentityStatement` in
  `RationalWeakExpansionTargets` specify the VI.3 expansion of the
  weighted weak constant terms of individual coefficients and its
  orbit integral for a proper standard target parabolic. They use
  actual compact lifts, `SourceCompactNormalization`, regular
  `WeightedCExtension` families with `IsWeightedCSection`, and
  `lowerCharacterMeasure` transported from the I.1 character Haar.
- The remaining VI.4.1(ii) input is the calculation of the ordinary
  induced constant term of the Schwartz packet. For semistandard
  \(P'=MU'\) with the same literal Levi, this calculation gives, for
  every \(g_1,g_2\in G\) and \(m\in M\),
  \[
  f_v^{(P'),\mathrm{Ind}}(g_1,g_2)(m)
  = \gamma(G\mid M)c(G\mid M)^2
    \sum_{s\in W(G\mid M)} f^M_{v^{s,g_1,g_2}}(m),\qquad
  v^{s,g_1,g_2}_{s\omega}
    = ({}^\circ c_{P'\mid P}(s,\omega)v_\omega)(g_1,g_2).
  \]
  The left side is the modulus-normalized integral over \(U'\) of
  the two-sided translate \(\rho(g_1)\lambda(g_2) f_v\), with
  \(K\cap U'\) of mass one. The right side uses smooth sections on
  \(s\mathcal O\), density \(1\) for the full Levi of \(M\), and the
  transported source-normalized orbit measure inside \(M\).
  The source proof exhausts \(U'\) by conjugates of a compact open
  subgroup, proves that the positive part tends to zero, and
  computes the limit of the weak part. The intertwiner limit in
  assertion (8) yields the normalized V.3 comparison and
  \(\gamma(G\mid M)c(G\mid M)^2\). The Library provides the abstract
  `tendsto_inv_mul_setIntegral_comp`,
  `tendsto_inv_smul_integral_of_local_basis`, and
  `eq_sum_integral_of_tendsto` for the exhaustion, positive-part
  vanishing, and orbit limit. Applying them requires the actual
  contraction and Haar scaling, the local coefficient estimates,
  and the measurable, uniformly bounded intertwiner integrands
  with the almost-everywhere limit in (8).
- `rationalInducedFourierTransform_eq_rationalConstantTermInducedFourierTransform`
  in `RationalInducedConstantTermFourier` proves VII.1.2 on actual
  standard points. Its hypotheses retain the Levi coefficient bound,
  ambient and Levi square-integrable weights, constant-term
  convergence and Schwartz output, and the common compact
  factorization and mass-one measures on \(K\), \(K\cap M\), and
  \(K\cap U\). Its evaluation lemma
  `eval_rationalConstantTermInducedFourierTransform` applies the
  Levi Fourier transform to `rationalConstantTerm` of the two-sided
  translate. The VII.2.1 route uses the VI.4.1(ii) calculation with
  \(P'=P\) here and applies the full-Levi Fourier calculation to the
  resulting packets on \(M\).
  `RationalSemistandardFourierStandardComparisonStatement` gives the
  exact comparison of the standard and intrinsic Fourier products
  with their compact and formal-degree normalizations. Reusing the
  full-Levi theorem inside \(M\) requires identifying the actual
  lower packets with its source-normalized models and checking its
  analytic and quotient-measure hypotheses there.

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques
(d’après Harish-Chandra)*, J. Inst. Math. Jussieu 2 (2003), 235–333.
VII.2.1, printed pp. 317–318 / PDF pp. 83–84, gives the conclusion.
I.1, V.1, V.3 and VI.1, printed pp. 238–240, 288, 295–296 /
PDF pp. 4–6, 54, 61–62, give the measure, quotient, comparison and
coherence conventions. III.6, printed p. 272 / PDF p. 38, defines the
ordinary induced constant term. VI.3, printed pp. 303–304 /
PDF pp. 69–70, gives the weighted weak-coefficient inputs. VI.4.1(ii)
is on printed p. 306 / PDF p. 72 and its proof spans printed
pp. 306–313 / PDF pp. 72–79. VII.1.2 is on printed p. 315 /
PDF p. 81. [Registered source](https://doi.org/10.1017/S1474748003000082)
