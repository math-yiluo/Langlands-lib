# Waldspurger VII.2.5: the isometry of the actual invariant synthesis

This module states the first assertion of Theorem VII.2.5 of Waldspurger
(2003) for the Library's actual invariant spectral space, weighted synthesis
and integral Hermitian form. It proves the elementary consequences and
equivalent formulations listed below. It does not prove the isometry.

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques
(d'après Harish-Chandra)*, J. Inst. Math. Jussieu 2 (2003), 235–333,
registered as `waldspurger-2003-plancherel`. Printed page = PDF page + 234.

- End of VII.2, printed p. 319 / PDF p. 85: for
  \(\psi,\psi'\in C^\infty(\Theta)_{\mathrm{inv}}\),
  \[
  (\psi',\psi)=\sum_{(\mathcal O,P=MU)\in\Theta}
  c(G\mid M)^{-2}\gamma(G\mid M)^{-1}|W^M||W^G|^{-1}|\mathcal P(M)|^{-1}
  \int_{\mathcal O}\mu(\omega)\,(\psi'[\mathcal O,P]_\omega,\psi[\mathcal O,P]_\omega)\,d\omega .
  \]
- VII.1, printed p. 313 / PDF p. 79: \((f_1,f_2)_G=\int_G\overline{f_1(g)}f_2(g)\,dg\).
- Remark VII.2.4, printed p. 320 / PDF p. 86: the same synthesis and form as
  sums over representatives of the association classes, with coefficient
  \(c(G\mid M)^{-2}\gamma(G\mid M)^{-1}|\mathrm{Stab}(\mathcal O,M)|^{-1}\),
  where \(\mathrm{Stab}(\mathcal O,M)=\{s\in W(G\mid M);\ s\mathcal O=\mathcal O\}\).
- Theorem VII.2.5, printed p. 320 / PDF p. 86: «L'application \(\kappa\) est
  une isométrie de \(C^\infty(\Theta)_{\mathrm{inv}}\) sur son image.» The
  proof cites Propositions VII.2.1, VII.2.2, Corollary VII.2.3 and Lemma VII.1.4.

## The target

Names are written relative to the namespaces opened by the module:
`Langlands.HarishChandraSchwartz` and its sub-namespace `RationalSemistandard`,
`Langlands.GroupScheme`, `Langlands.Plancherel`,
`Langlands.Plancherel.WaldspurgerSourceNormalization` (for `IsSourceCompactAt`)
and `Langlands.BruhatTits.SpecialCompact` (for `SpecialCompactProperties`). The
declarations of this module are in `RationalSemistandard.SynthesisIsometry`.

`SynthesisIsometry.SynthesisIsometryStatement hG a ha mu d hindex C Q hK hPK rho`
asserts, for all \(\psi',\psi\) in `rationalSemistandardThetaInvariantSections C`,

```
HarishChandraSchwartz.pairing (RationalDynamicSource.ambientHaar K hK) (κ ψ') (κ ψ)
  = GlobalForm.invariantGlobalForm hG a ha mu d C.presentation hindex Q K hK C ψ' ψ
```

with `κ = GlobalSynthesis.invariantSynthesis hG a ha mu d C.presentation hindex
Q K hK C hi hfin hK hPK rho hmem hnu hspecial hd hQ`. The left side is the
Bochner integral \(\int_G\overline{\kappa(\psi')(g)}\,\kappa(\psi)(g)\,dg\) of
`HarishChandraSchwartz.pairing`. The right side is the actual sum over the
finite support of \(\psi\) of the unquotiented source coefficient
`GlobalSynthesis.sourceWeight` times the density-weighted orbit integral of the
inverse-formal-degree coefficient pairing `GlobalForm.componentForm`. The form
is conjugate linear in its first argument, as is the integral. No form on the
spectral space is defined by pulling back along `κ`.

The objects are the actual ones of the Library:

- the invariant carrier `rationalSemistandardThetaInvariantSections C` of
  finite-support coherent smooth families satisfying `IsWeylInvariant` for the
  normalized comparison of `WeylSectionComparisonData`;
- the synthesis `invariantSynthesis`, the restriction of the actual
  Schwartz-valued weighted sum `schwartzSynthesis` of the source packets
  \(f_{\psi[\mathcal O,P]}\) with coefficient
  \(c(G\mid M)^{-2}\gamma(G\mid M)^{-1}|W^M|/(|W^G||\mathcal P(M)|)\);
- the form `invariantGlobalForm`, the restriction of `GlobalForm.rawGlobalForm`
  with the same coefficient, the actual density `GlobalForm.componentDensity`
  and the source orbit measure `SourceMeasure.normalizedOrbitMeasure`, which
  carries the I.1 character scale and the reciprocal cardinality of the
  self-twist stabilizer;
- the Haar measure `RationalDynamicSource.ambientHaar K hK` of mass one on `K`.

One compact open `K` is used for the Schwartz weights `rationalXi hK hPK`, for
the Haar measure, for the source constants and, through the premises `hd` and
`hQ`, for all compact pictures and scalar data. This is the situation of the
published VII.2.1–VII.2.3 targets of `WavePacketPairing`. The cocharacter
presentation of each Levi is the presentation `C.presentation` of the
comparison data, as in `Association.AssociationFormulaStatement`.

### Premises

Every input is a premise of the proposition, in this order:

| Premise | Content |
| --- | --- |
| `hi : IsMaximalSplitTorus i` | the fixed split torus is maximal |
| `hfin : SemistandardSpectralFiberFinitenessStatement` | the parabolic fibers of the semistandard Levis are finite and nonempty (geometric structural statement) |
| `hnu : IsGenericCocharacter i nu` | the cocharacter of the minimal parabolic of the Iwasawa pair is generic |
| `hspecial : SpecialCompactProperties F i nu K` | the special-compact properties of `K` |
| `hd`, `hQ` | every compact picture `d p` and all scalar data `Q t` use `K` |
| `hmem : SchwartzMembershipStatement …` | VI.3.1: the raw weighted sum `weightedSynthesis` of every smooth finite-support family, invariant or not, lies in the Schwartz submodule; this explicit membership premise is what makes `κ` Schwartz-valued |
| `IsSourceCompactAt i K` | `K` is a maximal compact open subgroup and the norm-one fixer of a special vertex of an \(\Omega\)-compatible apartment of the maximal split torus |
| `∀ p, WavePacketPairing.SourceLeviQuotientHaar a mu p` | the quotient Haar of \(M/A_M\) gives the image of \(K\cap M\) mass one (I.1) |
| `SquareIntegrableWeight (ambientHaar K hK) …` | the `L²` weight condition of Lemma II.1.5 |
| `GlobalForm.DensityNonnegative …` | at every orbit point the actual density is a nonnegative real number (V.2.1); zeros are allowed. Formula (1) of the proof of VII.2.2, `WavePacketPairing.packet_pairing_eq_componentForm`, uses it |

The first seven premises are exactly those consumed by `invariantSynthesis`.
The source compact and quotient Haar premises are those of the published
VII.2.1 and VII.2.2 targets. The density may vanish; no positivity of the
density is a premise of the isometry. Apart from the explicit VI.3.1 membership
premise `hmem`, no premise asserts a Schwartz or closure property. No premise
asserts the isometry, an inverse or positivity of the form, and the data `C`
and `Q` contain none of these.

Two irreducibility conditions occur in the data; neither is irreducibility of
tempered parabolic induction, which is not assumed. The field `irreducible` of
`Langlands.Plancherel.ActualConjugateLeviCoherence.LeviNormalization`, carried by each
`C.normalization t`, is irreducibility of the discrete-series inducing
representation of the Levi. The field `irreducible` of `OrbitPacketData` is
irreducibility of unramified parabolic induction at the characters of a
nonempty open set (generic irreducibility), used for the continuation of the
density.

The setting is that of the dependencies: an arbitrary nonarchimedean local
field `F` (any characteristic, finite residue field), an affine locally finite
type connected reductive group scheme `G` (split or not, of any rank, the
rank-zero case included), field universe `u` and representation universe `uV`
independent, the canonical rational-point topology, and complex
`IrreducibleAdmissibleRep`s of the literal Levis in the `SmoothRep` category.

## Proved formulations and consequences

| Declaration | Content and proof |
| --- | --- |
| `SynthesisL2IsometryStatement` | The same premises, with the integral replaced by `inner ℂ (Space.toL2 hw (κ ψ')) (Space.toL2 hw (κ ψ))`, where `hw = rationalL2Weights K.isOpen hK hPK rho hsw` and `Space.toL2` is the continuous inclusion of the Schwartz space into \(L^2(G)\). |
| `synthesisIsometry_iff_l2` | The two targets are equivalent, by `Space.inner_toL2`. |
| `integrable_conj_synthesis_mul` | The integrand \(\overline{\kappa(\psi')}\kappa(\psi)\) is integrable, by `Space.integrable_conj_mul`. |
| `inner_toL2_synthesis` | The `L²` inner product of the images is the integral pairing. |
| `pairing_synthesis_self` | The diagonal integral is \(\lVert\kappa(\psi)\rVert_{L^2}^2\), by `Space.pairing_self`. |
| `pairing_synthesis_eq_form`, `inner_toL2_synthesis_eq_form` | The target at given premises, in integral and in `L²` form. |
| `norm_sq_toL2_synthesis`, `norm_sq_toL2_synthesis_eq_re` | Diagonal formula \(\lVert\kappa(\psi)\rVert_{L^2(G)}^2=B(\psi,\psi)\), as a complex equation and for real parts. |
| `invariantSynthesis_injective_of_isometry` | Given the target, `GlobalForm.PositiveFormStatement` and `GlobalForm.DensityPositiveDense`, `κ` is injective. If \(\kappa(\psi_1)=\kappa(\psi_2)\), then \(z=\psi_1+(-1)\psi_2\) has \(\kappa(z)=0\), so \(B(z,z)\) is the integral of zero, and the definiteness of the existing positive form `GlobalForm.invariantGlobalPositiveForm` gives \(z=0\). |
| `sourceCompactCompatibility_of_inputs` | `hspecial`, `hd`, `hQ` give `WavePacketPairing.SourceCompactCompatibility`, a premise of the VII.2.1–VII.2.3 targets. |
| `componentSchwartzMembership_of_schwartzMembership` | `hmem` gives `WavePacketPairing.ComponentSchwartzMembershipStatement`, also a premise there: the synthesis of `rationalSemistandardThetaSingle t v` is `sourceWeight t • componentPacket t v` (by `finsum_eq_single`), and the weight is positive by `SourceConstants.unquotientedWeight_pos`. |
| `schwartzMembership_of_componentSchwartzMembership` | Conversely, `ComponentSchwartzMembershipStatement` gives `SchwartzMembershipStatement`, by the finite sum `weightedSynthesis_eq_sum`. |

### Theorem VII.2.5 in the association-representative form of Remark VII.2.4

Remark VII.2.4 supplies the two representative formulas and their weights;
the isometry between the representative sums is the assertion of Theorem VII.2.5.

`coefficientAtRepresentative_eq` displays the coefficient
`Association.coefficientAtRepresentative C K hK t` as
`((cReal)^2)⁻¹ * (gammaReal)⁻¹ / Nat.card (WeylOrbitStabilizer a ha mu t _)`,
by reflexivity. `Association.WeylOrbitStabilizer` is \(\mathrm{Stab}(\mathcal O,M)\),
the stabilizer of the orbit in the literal \(W(G\mid M)\); it is distinct from
the finite self-twist stabilizer that enters the orbit measure.

`AssociationIsometryStatement` has the premises of the target and asserts, for
every choice `R : Association.Representatives a ha mu` of association
representatives,

```
pairing (ambientHaar K hK) (packetRepresentativeSum C K hK hindex Q R ψ')
    (packetRepresentativeSum C K hK hindex Q R ψ)
  = formRepresentativeSum C K hK hindex Q R ψ' ψ
```

with the representative sums of `Association`. Given the published
`Association.AssociationFormulaStatement C K hK hindex Q`,
`synthesis_eq_packetRepresentativeSum` identifies `κ ψ` with the representative
sum pointwise, and `synthesisIsometry_iff_association` proves that the two
isometry statements are equivalent (for the converse the representatives
`Representatives.ofQuotient` suffice). `associationIsometry_of_isometry` derives
`AssociationIsometryStatement` from `SynthesisIsometryStatement` through the
published `Association.associationFormula_of_transport`. Its additional
hypotheses are exactly the remaining ones of that theorem:
`SemistandardSpectralDynamicCoverageStatement`,
`SourceConstantParabolicIndependenceStatement`, and
`C.CoefficientTransportStatement`, `C.DensityTransportStatement Q`,
`C.PairingTransportStatement` of `WeylSectionComparisonData`. Its intrinsic
quotient normalization follows from `SourceLeviQuotientHaar` and `hd`.

## Proof of the target: source route and Library statements

This module states the isometry and does not prove it. Waldspurger derives it
from Propositions VII.2.1, VII.2.2, Corollary VII.2.3 and Lemma VII.1.4. Expanding
\((\kappa(\psi'),\kappa(\psi))_G\) as a finite double sum of packet pairings,
VII.2.2(i) removes the pairs with nonconjugate Levis and VII.2.2(ii) evaluates
the others as sums over \(W(M'\mid G\mid M)\) of orbit integrals of the
normalized comparisons \({}^\circ c_{P'\mid P}(s,\omega)\). Invariance of \(\psi\)
and the count of Weyl elements and parabolics turn the double sum into
\((\psi',\psi)\). The proof of VII.2.2 itself uses formula (1), VII.1.4 and
VII.2.1, and VII.2.3 follows from VII.2.2(i) by detection with the positive
form.

The corresponding declarations of the Library, namespace `WavePacketPairing`
unless stated otherwise, and their inputs beyond the premises of this target:

| Source | Library declaration | Further inputs |
| --- | --- | --- |
| Proposition VII.2.1 | `FourierWeylSumStatement` | parameters of the Fourier family: the `L²` weight condition, `hdelta : ∀ p, ModularNormalization p` at every parabolic, and `hT`, tempered coefficients (`HasTemperedCoefficients`) of the normalized induction of every square-integrable inducing object; premises `SourceCompactCompatibility`, `IsSourceCompactAt`, `SourceLeviQuotientHaar`, `ComponentSchwartzMembershipStatement`; at each index a Levi normalization with `LeviNormalizationMatches` and `OrbitWeylDescentStatement` |
| Proposition VII.2.2 (i) | `NonconjugatePairingStatement` | premises `IsMaximalSplitTorus`, `IsGenericCocharacter`, `SourceCompactCompatibility`, `ComponentSchwartzMembershipStatement` |
| Proposition VII.2.2 (ii) | `ConjugatePairingStatement` | premises `IsMaximalSplitTorus`, `IsGenericCocharacter`, the `L²` weight condition, `SourceCompactCompatibility`, `IsSourceCompactAt`, `SourceLeviQuotientHaar`, `ComponentSchwartzMembershipStatement`; at each pair a Levi normalization with `LeviNormalizationMatches`, `OrbitWeylDescentStatement` and `OrbitWeylDensityTransportStatement` |
| Formula (1) in the proof of VII.2.2 | `packet_pairing_eq_componentForm` | `GlobalForm.DensityNonnegative`; `OrbitProductIntegrabilityStatement` at the index (the VI.2.2 double integrability); coherent smoothness of the Fourier component, `rationalSemistandardFourierFamily … f t ∈ rationalSemistandardThetaComponentSpace … t`, which `RationalSemistandardFourierFamilySmoothnessStatement` concludes under `RationalSemistandardFourierAnalyticInputs`; the Fourier-family parameters `hdelta` and `hT` |
| Corollary VII.2.3 | `PointwiseVanishingStatement`, `ComponentVanishingStatement` (equivalent by `pointwiseVanishing_iff_componentVanishing`) | parameters `hdelta`, `hT`, the `L²` weight condition and `ComponentSchwartzMembershipStatement`; premise `SourceCompactCompatibility`. `componentVanishing_of_nonconjugatePairing` derives `ComponentVanishingStatement` from `NonconjugatePairingStatement` with `GlobalForm.DensityNonnegative`, `GlobalForm.DensityPositiveDense`, `OrbitProductIntegrabilityStatement` at every index and coherent smoothness of every Fourier component |
| Lemma VII.1.4 | none | the covariance \(\psi_f[s\mathcal O,P'](s\omega)={}^\circ c_{P'\mid P}(s,\omega)\psi_f[\mathcal O,P](\omega)\) of `rationalSemistandardFourierFamily`; this module imports no statement of it |

A proof along this route also needs the comparison of the normalized sections
`normalizedWeylSection` of these statements with the comparison
`C.fiberComparison` defining the invariant carrier, and the common-Levi source
constants and Weyl counting used in `Association.associationFormula_of_transport`.

### The VI.3.1 membership premise

The premise `hmem` is the VI.3.1 membership of the actual weighted sums. Its
standard counterpart in the Library is
`StandardLeviPlancherelWavePacketMembershipStatement`, the membership clause of
`StandardLeviPlancherelWavePacketSourceNormalizedStatement`, for the
standard-Levi Plancherel wave packets at the I.1 character scale.
`StandardPacketComparison.packet_eq_standard` identifies the source packet
`OrbitPacketData.packetLinear` at a standard index, with the standard Levi
model, the standard compact data and the presentation
`StandardSourceComparison.presentation`, with that standard packet. Membership
at the other semistandard indices, for the chosen Levi models, the compact data
`d` and the presentation `C.presentation`, requires transport of packets by
conjugation and change of model and presentation; this transport is a separate
mathematical input, not supplied here. Membership of all component packets is
`WavePacketPairing.ComponentSchwartzMembershipStatement`;
`schwartzMembership_of_componentSchwartzMembership` assembles it into the
statement of `hmem`, and `componentSchwartzMembership_of_schwartzMembership`
gives the converse. The published
`GlobalSynthesis.schwartzMembership_of_componentContinuity` derives the
statement of `hmem` from the VI.3.1 continuity target
`GlobalSynthesis.ComponentContinuityStatement`.

This module asserts no finiteness of Fourier support, no surjectivity of `κ`
and no VIII.1 inversion.
