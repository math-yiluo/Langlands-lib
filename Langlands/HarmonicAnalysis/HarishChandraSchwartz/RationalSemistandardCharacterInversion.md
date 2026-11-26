# Waldspurger VIII.1 (3): the character inversion formula

This module states formula (3) of Waldspurger VIII.1 as a Prop-valued target, for
fixed data, for one group and for all groups. It proves that the integrand does not
depend on the choice of inducing objects, and that under VII.1.1 (iii) its orbit
integral is the source packet of `psi_f[O,P]`. Under the VII.2.4 association formula
it proves that (1) and (2) imply (3), and that (3) gives the reconstruction
`κ(psi_f) = f` whenever the invariant Fourier lift of `f` exists. With
invariant-carrier membership of every `psi_f` (`FourierInvariantLiftStatement`, which
contains smoothness, finite support and Weyl invariance) as a further hypothesis, (3)
is equivalent to (1) and (2) for the actual `κ`. Formula (3) itself is not proved.

Namespace: `Langlands.HarishChandraSchwartz.RationalSemistandard.FourierInversion`.
The module imports `RationalSemistandardFourierReconstruction`, which contains (1),
(2) and the invariant lift used below.

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques
(d'après Harish-Chandra)*, J. Inst. Math. Jussieu 2 (2003), registered as
`waldspurger-2003-plancherel` (SHA-256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`).

- VIII.1, printed p. 320 (PDF p. 86), formula (3): for every `f ∈ C(G)` and `g ∈ G`,
  `f(g) = Σ_{(O,P=MU) ∈ Θ/ass} c(G|M)^-2 γ(G|M)^-1 |Stab(O,M)|^-1
  ∫_O µ(ω) d(ω) θ^G_ω(λ(g) ˇf) dω`. The source says that, by Lemme VII.1.1 (iii) and
  Remarque VII.2.4, (3) is equivalent to (2).
- Remarque VII.2.4, printed p. 320: association of indices, a set `Θ/ass` of
  representatives, `Stab(O,M) = {s ∈ W(G|M); sO = O}`, and the sums over `Θ/ass`
  with coefficient `c(G|M)^-2 γ(G|M)^-1 |Stab(O,M)|^-1`.
- Lemme VII.1.1 (iii), printed p. 314 (PDF p. 80):
  `(E^G_P f̂(ω,P))(g) = d(ω) θ^G_ω(λ(g) ˇf)`. Here `ˇf(x) = f(x^-1)`,
  `λ(g)h(x) = h(g^-1 x)`, and `θ^G_ω` is the character of `I^G_P ω`.
- VII.1, printed p. 313: `f̂(ω,P)` is `d(ω)` times the element of `L(ω,P)` given by
  `π(ˇf)`, with `π = I^G_P ω`.

- I.1, printed p. 242 (PDF p. 8), and III.6, printed p. 271 (PDF p. 37): the height
  `σ` from an algebraic embedding into `GL_n` mapping `K` into `GL_n(O_F)`, and the
  Schwartz space `C(G)` defined with it.

`Stab(O,M)` is the Weyl orbit stabilizer of Remarque VII.2.4. It is distinct from the
unramified self-twist stabilizer in the I.1 orbit measure, which enters through the
normalized orbit measure.

## Objects

The variables are those of the full Fourier family (`hG hi hnu hKc hPK rho hsw a ha mu
d hdelta hT`), then `C`, `hindex`, `Q` (typed by `C.presentation`) and `K0 hK0`.

- `formalDegreeCharacter t A f g` is `d(ω) θ^G_ω(λ(g) ˇf)` at an actual inducing
  object `A` of the orbit of `t`. It is the formal degree `componentFormalDegree` for the
  actual split-central quotient Haar measure `mu t.1` (the degree in the definition of
  `psi_f`), times `semistandardInducedSchwartzCharacter`. That character is the trace
  of the actual finite-rank normalized induced Schwartz action, applied to
  `Space.translate _ 1 g (Space.check _ _ f)`, which is `λ(g) ˇf`.
- `OrbitSelection t`: a choice of an actual inducing object over every point of the
  orbit of `t` (a section of `componentOrbitPoint`). `OrbitSelection.choose` shows that
  selections exist.
- `characterIntegrand t s f g ω = µ(ω) · d(ω) θ^G_ω(λ(g) ˇf)`, at the selected object
  `s ω`. Here `µ` is `GlobalForm.componentDensity`, the density of the source packets
  and of the global form. No positivity of `µ` is assumed.
- `characterOrbitIntegral t s f g`: its integral for `componentOrbitMeasure`. This is
  the normalized I.1 orbit measure of the source packets, with the unitary character
  Haar scale and self-twist factor of the Library's source measure.
- `characterInversionSum R s f g`: the sum over a set `R` of association
  representatives (`Association.representativeSum`) of
  `Association.coefficientAtRepresentative`, which is
  `c(G|M)^-2 γ(G|M)^-1 |Stab(O,M)|^-1`, times the orbit integral.

## The target

`CharacterInversionStatement`: for every Schwartz `f`, every `g`, every set `R` of
association representatives and every selection `s`, three things hold. Each orbit
integrand (at every index, not only at the representatives) is integrable. Only
finitely many association classes have a nonzero term. And
`f g = characterInversionSum R s f g`. The target concludes convergence and finiteness;
it assumes neither.

`RationalLocalCharacterInversionStatement G` asserts the target for one group and for
all source data with the I.1 normalizations: one source special compact `K`
(`IsSourceCompactAt`), used as the Schwartz compact and, through `hd` and `hQ`, as the
compact of every compact picture and scalar datum; a height from a matrix
representation `rho` that is a closed embedding (`IsClosedSubgroup rho`) with `K` in its
integral subgroup (`K ≤ rationalHeightSubgroup rho`), as in I.1 (printed p. 242), so that
the Schwartz space is the space `C(G)` of III.6 (printed p. 271); the Haar measure
`RationalDynamicSource.ambientHaar K hK`; and the quotient Haar condition
`WavePacketPairing.SourceLeviQuotientHaar`. `RationalCharacterInversionGlobalStatement`
is its closure over all fields and groups. The field may have positive
characteristic. The group need not be quasi-split, and its rank may be zero.

## Proved relations

The fixed-data target and the relations below allow any matrix representation `rho`
with the weight condition; the local and global targets use the source height.

- `formalDegreeCharacter_eq_coefficient` (VII.1.1 (iii)): `d(ω) θ^G_ω(λ(g) ˇf)` is the
  value at `g` of `rationalSemistandardFourierCoefficientMap` applied to the component
  `psi_f[O,P](ω)`. It is the Library's `rationalSemistandardFourier_trace`.
- `formalDegreeCharacter_eq_of_point_eq`: two inducing objects with the same orbit
  point give the same value. The proof takes an equivalence between them from the
  equality of classes. Then it uses the representative coherence
  `rationalSemistandardFourierFamily_coherent` (which needs `muG.IsInvInvariant`), the
  transport invariance `CompactInduction.coefficientMap_transport`, and the previous
  item twice.
- `characterIntegrand_selection_independent` and
  `characterOrbitIntegral_selection_independent`: the integrand and the integral do
  not depend on the selection.
- `characterIntegrand_eq_packetIntegrand`: if `psi_f[O,P]` is a smooth section, the
  integrand equals `µ(ω) (E^G_P psi_f[O,P](ω))(g)`, the integrand of the source packet.
  The proof uses `SourcePacket.coefficientMap_representative` and VII.1.1 (iii).
- `integrable_characterIntegrand`: then the integrand is integrable. It is continuous
  on the compact orbit, by `SourceForm.continuous_orbitDensity` and
  `SourcePacket.continuous_coefficient`.
- `componentPacket_eq_characterOrbitIntegral`: then the source packet of
  `psi_f[O,P]` at `g` equals the orbit integral of (3).
- `support_characterSummand_subset`: if every component is smooth, the indices with a
  nonzero term lie in the literal support of `psi_f`.
- `weightedSynthesis_eq_characterInversionSum`: assume
  `Association.AssociationFormulaStatement` (VII.2.4) and invariant-carrier membership
  of `psi_f`. Then the weighted synthesis of `fourierInvariantLift f hf`, which is
  `κ(psi_f)`, equals the right side of (3) at `g`. This holds for every `R` and every
  selection.
- `characterInversion_of_fourierInversion`: under VII.2.4,
  `FourierInversionStatement` ((1) and (2)) implies (3).
- `synthesisReconstruction_of_characterInversion`: under VII.2.4, (3) implies the
  reconstruction `SynthesisReconstructionStatement`.
- `characterInversion_iff_fourierInversion`: under VII.2.4 and
  `FourierInvariantLiftStatement` (invariant-carrier membership of every `psi_f`),
  (3) is equivalent to `FourierInversionStatement`.

## Inputs

Besides the structural and analytic inputs of the Fourier family and the packets,
listed in `RationalSemistandardFourierReconstruction`, the comparison uses exactly two
inputs. One is the VII.2.4 target `Association.AssociationFormulaStatement`. The other
is the invariant-carrier membership `FourierInvariantMembership`, which carries
smoothness, finite support and Weyl invariance. Representative independence uses
inversion invariance of `muG`.

## Declaration-level dependency map

- `formalDegreeCharacter` → `componentFormalDegree`, `semistandardInducedSchwartzCharacter`.
- `formalDegreeCharacter_eq_coefficient` → `rationalSemistandardFourier_trace`.
- `formalDegreeCharacter_eq_of_point_eq` → `rationalSemistandardFourierFamily_coherent`,
  `CompactInduction.coefficientMap_transport`.
- `characterIntegrand`, `characterOrbitIntegral` → `GlobalForm.componentDensity`,
  `componentOrbitMeasure`, `componentOrbitPoint`.
- `characterInversionSum` → `Association.representativeSum`,
  `Association.coefficientAtRepresentative`.
- `characterIntegrand_eq_packetIntegrand` → `SourcePacket.coefficientMap_representative`.
- `integrable_characterIntegrand` → `SourcePacket.sourceOrbit_compactSpace`,
  `SourceForm.continuous_orbitDensity`, `SourcePacket.continuous_coefficient`.
- `weightedSynthesis_eq_characterInversionSum` →
  `Association.AssociationFormulaStatement`,
  `Association.packetRepresentativeSum_eq_finiteSum`,
  `Association.representativeSum_eq_sum`, `fourierInvariantLift`.
- `characterInversion_iff_fourierInversion` → `fourierInversionStatement_iff`,
  `Association.support_representativeSummand_subset`.
- `RationalLocalCharacterInversionStatement` → `IsSourceCompactAt`,
  `RationalDynamicSource.ambientHaar`, `WavePacketPairing.SourceLeviQuotientHaar`,
  `sourceAmbientHaar_isMulRightInvariant`.
