# Waldspurger VIII.1 (1) and (2): Fourier support and synthesis reconstruction

This module states, as Prop-valued targets, the support and reconstruction
assertions (1) and (2) of Waldspurger VIII.1 for the actual full Fourier family
`psi_f` and the actual synthesis `κ`. The standalone finite-support target (1) is
stated for fixed data and for one group. Reconstruction by `κ` and the combined
inversion target ((1) and (2) together) are stated for fixed data and for one group;
the combined target also has a closure over all groups. The unquotiented
reconstruction formula (2) and its zero case, the injectivity of `f ↦ psi_f`, have
forms for fixed data, for one group, for all groups and for all groups of relative
semisimple rank below a bound. The module proves only the elementary relations
between these targets. It does not prove (1), (2), their zero case, VII.1.3, VII.1.4,
VII.2.5 or VIII.1.2.

Namespace: `Langlands.HarishChandraSchwartz.RationalSemistandard.FourierInversion`.

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques
(d'après Harish-Chandra)*, J. Inst. Math. Jussieu 2 (2003), 235–333, registered
as `waldspurger-2003-plancherel` (SHA-256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`). Printed page
= PDF page + 234.

- VIII.1, printed p. 320 (PDF p. 86). Théorème VIII.1.1 says that `κ` is surjective.
  The text says that, by Théorème VII.2.5, this is equivalent to (1) and (2) together:
  (1) for every `f ∈ C(G)` the set of `(O,P) ∈ Θ` with `psi_f[O,P] ≠ 0` is finite;
  (2) for every `f ∈ C(G)`,
  `f = Σ_{(O,P=MU) ∈ Θ} c(G|M)^-2 γ(G|M)^-1 |W^M| |W^G|^-1 |P(M)|^-1 f_{psi_f[O,P]}`.
  The sum in (2) has a meaning only under (1).
- VIII.2.1, printed pp. 321–322 (PDF pp. 87–88). The proof applies (2) to a proper
  Levi subgroup `M`, which has strictly smaller semisimple rank, and to the function
  `f_M`. All Fourier components of `f_M` vanish there, so `f_M = 0`. This is the zero
  case of (2) for `M`. The induction hypothesis stated just before VIII.2 (printed
  p. 321) assumes VIII.1.1 and VIII.1.2 for groups of strictly smaller rank.
- I.1, printed p. 240 (PDF p. 6): every closed algebraic subgroup `H` of `G` carries the Haar
  measure with `mes(H ∩ K) = 1`, where `K` is the maximal compact fixing a special
  point of the apartment of `A_0`.
- I.1, printed p. 242 (PDF p. 8), and III.6, printed p. 271 (PDF p. 37): the height
  from an algebraic embedding into `GL_n` mapping `K` into `GL_n(O_F)`, and the Schwartz
  space `C(G)` defined with it.
- VI.3 and VII.1–VII.2 for `C^∞(Θ)`, `C^∞(Θ)_inv`, `f_ψ`, `psi_f` and `κ`, as
  realized in the Library (below).

## Library objects used

- The full Fourier family `rationalSemistandardFourierFamily` (module
  `RationalSemistandardFourierFamily`). Its component at `(O,P)` and at an inducing
  object `ω` is `d(ω)` times the tensor of the normalized induced operator at `ˇf`.
  It lies in the dependent product `RationalSemistandardThetaSections`.
- The finite-support smooth families `rationalSemistandardThetaSmoothSections`
  (`C^∞(Θ)`), the components `rationalSemistandardThetaComponentSpace`, and
  the invariant carrier `rationalSemistandardThetaInvariantSections C` (`C^∞(Θ)_inv`),
  defined by the pointwise relation `IsWeylInvariant C`.
- The weighted synthesis `GlobalSynthesis.weightedSynthesis`, its source packets
  `componentPacket` and the unquotiented source coefficient `sourceWeight`. The
  coefficient is `c(G|M)^-2 γ(G|M)^-1 |W^M| / (|W^G| |P(M)|)`, with every parabolic
  of the fiber of `M` counted. The Schwartz-valued synthesis
  `GlobalSynthesis.invariantSynthesis` (`κ`) is defined from the VI.3.1 membership
  target `SchwartzMembershipStatement`.
- The support target `RationalSemistandardFourierFiniteSupportStatement` (VIII.1 (1)),
  the smoothness target `RationalSemistandardFourierFamilySmoothnessStatement` with
  its inputs `RationalSemistandardFourierAnalyticInputs` (VII.1.3), and the
  component lemma `rationalSemistandardFourierFamily_mem_componentSpace_of_smoothness`
  (module `RationalSemistandardFourierThetaSupport`).
- The proved geometric finiteness `semistandardSpectralFiberFiniteness`, used as the
  fiber-finiteness argument of `κ`. The proved rank decrease
  `semistandardProperLeviRank` with `semistandardLeviSplitTorus` and
  `isMaximalSplitTorus_semistandardLeviSplitTorus`.
- The source compact `IsSourceCompactAt`, the I.1 quotient Haar condition
  `WavePacketPairing.SourceLeviQuotientHaar` (module
  `RationalSemistandardWavePacketFourier`), the Haar measure
  `RationalDynamicSource.ambientHaar K hK` of mass one on `K`, and
  `Langlands.Haar.isMulRightInvariant_of_modularCharacter_eq_one` with
  `ambient_modularCharacter`.

## Fixed-data targets and their relations

The variables are those of the full Fourier family: `hG hi hnu hKc hPK rho hsw` and
`a ha mu d hdelta hT`. The unquotiented section adds the raw synthesis data
`rs hindex Q K0 hK0`. The invariant section adds the comparison data `C`, with
`Q` typed by `C.presentation`, the source compact `K0`, the membership witness
`hsynth`, and `hspecial hd hQ`. The Haar measure `muG` of the Fourier family is
arbitrary here; the local targets below fix it.

### The zero case

- `FourierInjectivityStatement`: `psi_f = 0` implies `f = 0`, for every Schwartz `f`.
  It uses the Fourier data only. `fourierInjectivityStatement_iff` identifies it
  with injectivity of the linear map `f ↦ psi_f`.

### Formula (2) without the Weyl quotient

- `unquotientedReconstructionSum f hsm hfs g` is the right side of (2) at `g`. It is the
  sum over the finite literal support of `psi_f` of `sourceWeight` times the source
  packet of the component `psi_f[O,P]`. The witness `hsm` (smooth components) types
  the packets; the witness `hfs` (finite support) controls the sum.
- `fourierSmoothLift f hsm hfs`: the element of `C^∞(Θ)` whose underlying family is
  `psi_f` itself (`fourierSmoothLift_val`).
  `unquotientedReconstructionSum_eq_weightedSynthesis` shows that the sum is the
  weighted synthesis of this lift.
- `UnquotientedReconstructionAt f`: for all witnesses `hsm`, `hfs` and every `g`,
  `f(g)` equals the unquotiented sum. `UnquotientedReconstructionStatement` asserts
  it for every `f`. Finite support is a visible premise, not a conclusion.
  `unquotientedReconstructionAt_iff` restates it as equality of `f` with the
  weighted synthesis of the smooth lift.
- `eq_zero_of_fourierFamily_eq_zero` and
  `fourierInjectivity_of_unquotientedReconstruction`: the unquotiented formula gives
  its zero case. With `psi_f = 0` both witnesses hold trivially, and the lift is zero.

### The invariant lift and `κ`

- `FourierInvariantMembership C f`: `psi_f ∈ C^∞(Θ)` and `IsWeylInvariant C psi_f`.
  `fourierInvariantMembership_iff` splits it into smooth components, finite literal
  support and pointwise Weyl invariance.
- `fourierInvariantLift f hf`: the element of `C^∞(Θ)_inv` with underlying family
  `psi_f` (`fourierInvariantLift_val`). It is not a selected preimage.
  `fourierInvariantLift_congr` shows that it does not depend on the witness, and
  `fourierInvariantLift_eq_of_fourierFamily_eq` that it depends only on `psi_f`.
- `FourierInvariantLiftStatement C`: every `psi_f` lies in `C^∞(Θ)_inv`.
  `fourierInvariantLiftStatement_iff` shows that this is exactly the conjunction of
  componentwise smoothness for every `f` (the conclusion of VII.1.3),
  `RationalSemistandardFourierFiniteSupportStatement` (VIII.1 (1)), and
  `IsWeylInvariant C psi_f` for every `f` (the conclusion of VII.1.4).
  `fourierInvariantLiftStatement_of_smoothness` derives it from the published
  smoothness target, its analytic inputs at every component, the support target and
  the invariance.
- `invariantSynthesis_fourierInvariantLift_apply`: under a membership witness,
  `κ(psi_f)(g)` is the unquotiented sum at `g`.
- `SynthesisReconstructionAt f`: for every membership witness,
  `κ(fourierInvariantLift f hf) = f`. `SynthesisReconstructionStatement` asserts it
  for every `f`. This is (2) for the actual `κ`; membership is a visible premise.
- `invariantSynthesis_fourierInvariantLift_eq_iff`: under a witness, `κ(psi_f) = f`
  is the pointwise unquotiented formula.
  `synthesisReconstructionAt_of_unquotiented`,
  `unquotientedReconstructionAt_of_synthesisReconstructionAt` (at an `f` whose
  `psi_f` is Weyl invariant), `synthesisReconstruction_of_unquotiented` and
  `synthesisReconstruction_iff_unquotiented` (given invariance of every `psi_f`)
  compare the two forms of (2).
- `FourierInversionStatement`: every `f` has a membership witness `hf` with
  `κ(fourierInvariantLift f hf) = f`. This is (1) and (2) together.
  `fourierInversionStatement_iff` shows that it is the conjunction of
  `FourierInvariantLiftStatement` and `SynthesisReconstructionStatement`, and
  `surjective_of_fourierInversion` gives surjectivity of `κ`.

Finite support alone does not give reconstruction: no statement here derives (2)
from (1).

## Local targets for one group and their closures

A local target fixes the field `F` and the group `G`, with `[IsAffineHom G.X.hom]`
and `[LocallyOfFiniteType G.X.hom]`. It quantifies over the connected reductivity of
`G` and over all remaining data. The field may have positive characteristic. The
group need not be split or quasi-split, and its rank may be zero. The carrier universe
`uV` is independent of the field universe `u`.

- `RationalLocalFourierFiniteSupportStatement G` and
  `RationalLocalFourierInjectivityStatement G` quantify over the Fourier data only: a
  maximal split torus and generic cocharacter, any compact open `K` in an Iwasawa
  pair, any matrix representation `rho` for the height, any Haar measure `muG` on
  `G(F)` (with right invariance), the weight condition `hsw`, the split components, any
  split-central quotient Haar measures, compact data, modular normalizations and
  induced temperedness. They have no synthesis data and no normalization premise. The
  source choices (a closed matrix embedding integral on the source special compact,
  the measures of I.1) are special cases, so the source statements follow by
  specialization. These targets also apply directly to the Levi data of
  `RationalSemistandardLeviFourierData`, whose compact and height are not assumed to be
  of source type. Their conclusions do not depend on
  these scales, component by component. Rescaling the Haar measure of `G(F)` by a
  positive factor multiplies every Fourier component by that factor. Rescaling the
  split-central quotient Haar measure at one parabolic `P` by a positive factor
  divides the formal degree, hence the components over `P`, by that factor, after the
  canonical transport of the orbits and their fibers; the components over other
  parabolics keep their own factors. So the literal support of `psi_f` and the
  condition `psi_f = 0` are invariant under these changes.
- `RationalLocalUnquotientedReconstructionStatement G`,
  `RationalLocalSynthesisReconstructionStatement G` and
  `RationalLocalFourierInversionStatement G` use the I.1 normalizations. One compact
  `K` is the source special compact (`IsSourceCompactAt i K`). It is also the compact
  of the Schwartz space and, through `hd` and `hQ`, of every compact picture and
  scalar datum. For `κ` it serves as `Kbase` and as `K0`. The height comes from a matrix representation `rho` that is a closed embedding
  (`IsClosedSubgroup rho`) with `K` in its integral subgroup
  (`K ≤ rationalHeightSubgroup rho`), as in I.1 (printed p. 242), so the Schwartz space is
  the space `C(G)` of III.6 (printed p. 271). The Haar measure of `G(F)`
  is `RationalDynamicSource.ambientHaar K hK`, of mass one on `K`. It is right
  invariant by unimodularity (`sourceAmbientHaar_isMulRightInvariant`). The quotient
  Haar measures satisfy `WavePacketPairing.SourceLeviQuotientHaar` for `K`. The
  synthesis data (`rs` or `C`, `hindex`, `Q`, and for `κ` the witnesses `hsynth`
  and `hspecial`) are quantified universally. No orbit finiteness, Fourier support,
  reconstruction, surjectivity or Plancherel conclusion for `G` is a premise.
- `rationalLocalSynthesisReconstruction_of_unquotiented` (with `rs := C.presentation`)
  and `rationalLocalSynthesisReconstruction_of_fourierInversion` relate the local
  targets.
- Closures over all fields and groups: `RationalFourierInversionGlobalStatement`,
  `RationalUnquotientedReconstructionGlobalStatement` and
  `RationalFourierInjectivityGlobalStatement`.

### Strictly lower rank

`RationalStrictlyLowerRankFourierInjectivityStatement n` and
`RationalStrictlyLowerRankUnquotientedReconstructionStatement n` assert the local
target for every connected reductive group whose relative root rank, measured with a
maximal split torus, is less than `n`. Their binders are those of the Library's
`RationalStrictlyLowerRankOrbitFinitenessStatement`. They name only groups of smaller
rank, so no same-rank theorem is needed to state them. For each family the module proves:

- `…_mono` and `…_zero`;
- `rationalFourierInjectivityGlobal_iff_all_rank_bounds` and
  `rationalUnquotientedReconstructionGlobal_iff_all_rank_bounds`;
- `rationalLocalFourierInjectivity_of_rank_lt` and
  `rationalLocalUnquotientedReconstruction_of_rank_lt`, the application at one group;
- `rationalLocalFourierInjectivity_properLevi_of_lowerRank` and
  `rationalLocalUnquotientedReconstruction_properLevi_of_lowerRank`. For every proper
  semistandard index `p` and every closed reductive model `m` of its literal Levi, the
  bound at the ambient rank gives the local target for `m.scheme`. The proof uses
  `semistandardProperLeviRank`. This is the form used in VIII.2.1. The injectivity
  form needs no synthesis data for the Levi subgroup.

## Input ledger

- Structural data: the maximal split torus and generic cocharacter; the Iwasawa pair
  and source compact; the split components with their normality and measurability
  instances; the compact data `d` with `hd`; the cocharacter presentations; the finite
  index `hindex`; the primitive scalar packet data `Q`
  (`OrbitPacketData`: reflection, central character, factorizations, continuations,
  irreducibility locus, regularity of `j_P^-1`) with `hQ`; and the comparison data `C`
  (`WeylSectionComparisonData`), which fixes the presentations, the intrinsic source
  normalization and the closed V.3 section comparisons.
- Normalizations: the source height (`IsClosedSubgroup rho`,
  `K ≤ rationalHeightSubgroup rho`), `IsSourceCompactAt`,
  `RationalDynamicSource.ambientHaar K hK` and
  `SourceLeviQuotientHaar` in the reconstruction targets.
- Preceding analytic inputs of the constructions: the weight condition `hsw`
  (II.1.5), the modular normalizations `hdelta`, temperedness of the normalized
  inductions `hT`, and the VI.3.1 membership witness `hsynth` for `κ`.
- Remaining substantive assertions, all unproved here: VII.1.3 smoothness
  (`RationalSemistandardFourierFamilySmoothnessStatement`), VII.1.4 covariance (the
  invariance `IsWeylInvariant C psi_f`), VIII.1 (1)
  (`RationalSemistandardFourierFiniteSupportStatement`), and the reconstruction and
  injectivity targets of this module.

## Declaration-level dependency map

- `unquotientedReconstructionSum` → `sourceWeight`, `componentPacket`,
  `rationalSemistandardFourierFamily`.
- `unquotientedReconstructionSum_eq_weightedSynthesis` → `weightedSynthesis_apply`.
- `FourierInvariantMembership`, `fourierInvariantLift` →
  `rationalSemistandardThetaSmoothSections`, `IsWeylInvariant`,
  `rationalSemistandardThetaInvariantSections`.
- `fourierInvariantLiftStatement_iff` → `RationalSemistandardFourierFiniteSupportStatement`;
  `fourierInvariantLiftStatement_of_smoothness` →
  `rationalSemistandardFourierFamily_mem_componentSpace_of_smoothness`.
- `SynthesisReconstructionStatement`, `FourierInversionStatement` →
  `invariantSynthesis`, `SchwartzMembershipStatement`,
  `semistandardSpectralFiberFiniteness`.
- The local reconstruction targets → `IsSourceCompactAt`,
  `RationalDynamicSource.ambientHaar`, `WavePacketPairing.SourceLeviQuotientHaar`,
  `sourceAmbientHaar_isMulRightInvariant`.
- The rank closures → `RationalPointFamily.exists_maximalSplitTorus_genericCocharacter`,
  `semistandardProperLeviRank`, `semistandardLeviSplitTorus`,
  `isMaximalSplitTorus_semistandardLeviSplitTorus`.
