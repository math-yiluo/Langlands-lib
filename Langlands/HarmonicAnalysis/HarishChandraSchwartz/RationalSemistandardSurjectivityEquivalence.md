# Waldspurger VIII.1: surjectivity of `κ` versus (1) and (2), under VII.2.5

This module proves the equivalences that Waldspurger states at the beginning of VIII.1.
Théorème VIII.1.1 (surjectivity of the synthesis `κ`) is equivalent to assertions (1)
and (2) together, by Théorème VII.2.5. The module also constructs the resulting
complex-linear equivalence `C^∞(Θ)_inv ≃ C(G)` and proves that it carries the
integral Hermitian form of `G` to the spectral form.

The module does not prove VII.1.4, VII.2.5 or VIII.1.1. VII.2.5 enters through its
Library targets `SynthesisInverse.SynthesisInverseStatement` (the second assertion,
`psi_(κ ψ) = ψ`) and `SynthesisIsometry.SynthesisIsometryStatement` (the first
assertion, the isometry). VII.1.4 enters through
`RationalSemistandardFourierCovarianceStatement`. Each is a hypothesis of the
theorems that use it. Componentwise smoothness of `psi_f` (VII.1.3) is a visible
hypothesis of the source-form theorem below.

The equivalences put surjectivity on one side of the conclusion and the joint inversion
conditions on the other. Surjectivity (VIII.1.1, `hsurj`) is also an explicit premise of
the one-way implications `fourierInversion_of_synthesisSurjectivity`,
`fourierInjectivity_of_synthesisSurjectivity` and
`unquotientedReconstruction_of_synthesisSurjectivity`. It is also a premise, as a section
variable, of the linear equivalence `synthesisLinearEquiv` and of every theorem about it.
Injectivity of `f ↦ psi_f` is an explicit premise of the one-way implication
`synthesisReconstruction_of_fourierInjectivity`. No theorem in the module takes
reconstruction or Fourier support as a hypothesis. The fiber finiteness used to build `κ`
is the proved `semistandardSpectralFiberFiniteness`. The synthesis is built from the
source synthesis and comparison data of the imported modules.

Namespace: `Langlands.HarishChandraSchwartz.RationalSemistandard.FourierInversion`.
The module imports `RationalSemistandardSynthesisSurjectivity` (and through it
`RationalSemistandardFourierReconstruction`), `RationalSemistandardSynthesisInverse`,
`RationalSemistandardSynthesisIsometry` and `RationalSemistandardFourierCovariance`.

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques
(d'après Harish-Chandra)*, J. Inst. Math. Jussieu 2 (2003), 235–333,
DOI 10.1017/S1474748003000082, registered as `waldspurger-2003-plancherel` (SHA-256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`). Printed page =
PDF page + 234.

- VIII.1, printed p. 320 (PDF p. 86): "Théorème VIII.1.1. L'application κ est
  surjective. En vertu du Théorème VII.2.5, cette assertion est équivalente aux
  assertions (1) et (2) suivantes": (1) for every `f ∈ C(G)`, only finitely many
  `(O,P) ∈ Θ` have `ψ_f[O,P] ≠ 0`; (2) for every `f ∈ C(G)`,
  `f = Σ_(O,P=MU)∈Θ c(G|M)^-2 γ(G|M)^-1 |W^M| |W^G|^-1 |P(M)|^-1 f_(ψ_f[O,P])`.
- Théorème VII.2.5, printed p. 320 (PDF p. 86): `κ` is an isometry of `C^∞(Θ)_inv` onto
  its image, and `ψ_(κ(ψ))[O,P] = ψ[O,P]` for every `ψ ∈ C^∞(Θ)_inv` and `(O,P) ∈ Θ`.
- Lemme VII.1.4, printed p. 317 (PDF p. 83): the Fourier family `ψ_f` is Weyl
  covariant. With Proposition VII.1.3 (smoothness, printed p. 316) and (1), this puts
  `ψ_f` in `C^∞(Θ)_inv`; the source uses this when it writes `κ(ψ_f)`.
- VII.1, printed p. 313 (PDF p. 79): the Hermitian form `(f', f)_G = ∫_G conj(f'(g)) f(g) dg`
  on `C(G)`.

Waldspurger states the equivalence in one sentence, without a separate proof. The
argument behind it, which the module formalizes, is the following. If `κ` is surjective, write `f = κ(ψ)`; then
`ψ_f = ψ` by VII.2.5, so `ψ_f` has finite support and `κ(ψ_f) = f`, which is (2)
by the definition of `κ`. Conversely, (1) and (2) say that `f = κ(ψ_f)`.

## Setting

All theorems are for fixed data with the I.1 normalizations used by the VII.2.5 targets:
one compact open `K` that is the source special compact (`hcompact : IsSourceCompactAt i K`),
the Schwartz compact, the compact `K0` of `κ`, and, through `hd` and `hQ`, the compact of
every compact picture and packet datum; the Haar measure of `G(F)` is
`RationalDynamicSource.ambientHaar K hK`; the split-central quotient Haar measures satisfy
`hhaar : ∀ p, WavePacketPairing.SourceLeviQuotientHaar a mu p`. The synthesis is
`κ = GlobalSynthesis.invariantSynthesis` with the proved fiber finiteness
`semistandardSpectralFiberFiniteness`, the presentations `C.presentation` and the VI.3.1
membership witness `hmem`. The Fourier family is `rationalSemistandardFourierFamily`.
The density hypotheses `hn : GlobalForm.DensityNonnegative …` and
`hdense : GlobalForm.DensityPositiveDense …` are premises of the VII.2.5 inverse
target and are passed to it. The instance
`(RationalDynamicSource.ambientHaar K hK).IsMulRightInvariant` is a section variable;
the Library proves it for connected reductive `G`
(`SynthesisInverse.sourceHaar_isMulRightInvariant`).

The hypothesis `hinv : SynthesisInverse.SynthesisInverseStatement …` is the VII.2.5
inverse target for these data. Its own premises are instantiated with the data above.

## Consequences of the VII.2.5 inverse

- `fourierFamily_invariantSynthesis`: `psi_(κ ψ) = ψ` in the full dependent product
  (`SynthesisInverse.fourier_synthesis`).
- `fourierInvariantMembership_invariantSynthesis`: `psi_(κ ψ)` satisfies
  `FourierInvariantMembership` (smooth components, finite support, Weyl invariance),
  since it equals `ψ`.
- `fourierInvariantLift_invariantSynthesis`: the invariant Fourier lift of `κ ψ` is `ψ`.

## The equivalences

- `fourierInversion_of_synthesisSurjectivity`: under `hinv`, surjectivity
  (`SynthesisSurjectivityStatement`) gives `FourierInversionStatement`, that is (1) and
  (2) in the form "every `psi_f` lies in `C^∞(Θ)_inv` and `κ(psi_f) = f`".
- `synthesisSurjectivity_iff_fourierInversion`: under `hinv`, surjectivity is
  equivalent to `FourierInversionStatement`. The converse direction is
  `synthesisSurjectivity_of_fourierInversion` and needs no VII.2.5 input.
- `synthesisSurjectivity_iff_lift_and_reconstruction`: under `hinv`, surjectivity is
  equivalent to the conjunction of the separate targets `FourierInvariantLiftStatement`
  (invariant-carrier membership of every `psi_f`) and
  `SynthesisReconstructionStatement` (`κ(psi_f) = f` for every membership witness).
- `synthesisReconstruction_of_fourierInjectivity`: under `hinv`, injectivity of
  `f ↦ psi_f` (`FourierInjectivityStatement`) gives reconstruction, since `κ(psi_f)`
  and `f` have the same Fourier family.
- `fourierInjectivity_of_synthesisSurjectivity`: under `hinv`, surjectivity gives
  injectivity of `f ↦ psi_f`.
- `synthesisSurjectivity_iff_lift_and_injectivity`: under `hinv`, surjectivity is
  equivalent to invariant-carrier membership of every `psi_f` together with
  injectivity of `f ↦ psi_f`.
- `unquotientedReconstruction_of_synthesisSurjectivity`: under `hinv`, surjectivity
  gives `UnquotientedReconstructionStatement`, the formula (2) as displayed in the
  source: at every `g`, `f(g)` is the sum over the finite literal support of `psi_f` of
  `c(G|M)^-2 γ(G|M)^-1 |W^M| |W^G|^-1 |P(M)|^-1 f_(psi_f[O,P])(g)`, with the actual
  source packets and coefficients.

Finite support alone is not among the conditions of any of these equivalences.
Invariant-carrier membership also contains componentwise smoothness and Weyl
invariance, and reconstruction (or injectivity) is a separate condition.

## The VII.1.4 adapter and the source form

These theorems also take `hcov : RationalSemistandardFourierCovarianceStatement …`,
the VII.1.4 target for the same data. Its premise
`SourceMeasure.IntrinsicQuotientNormalization a mu d` follows from `hd` and `hhaar`.

- `isWeylInvariant_fourierFamily_of_covariance`: every `psi_f` is Weyl invariant
  (`IsWeylInvariant C`), by `rationalSemistandardFourierCovarianceStatement_iff`.
- `fourierInvariantLiftStatement_iff_smoothSections_of_covariance`: under `hcov`,
  invariant-carrier membership of every `psi_f` is equivalent to membership of every
  `psi_f` in the coherent smooth finite-support carrier
  `rationalSemistandardThetaSmoothSections`.
- `synthesisSurjectivity_iff_smoothSections_and_reconstruction` and
  `synthesisSurjectivity_iff_smoothSections_and_injectivity`: under `hinv` and `hcov`,
  surjectivity is equivalent to smooth finite-support membership of every `psi_f`
  together with reconstruction, respectively with injectivity of `f ↦ psi_f`.
- `synthesisSurjectivity_iff_finiteSupport_and_unquotiented`: the sentence of VIII.1 in
  its source form. Under `hinv`, `hcov` and componentwise smoothness
  `hsm : ∀ f t, psi_f[t] ∈ rationalSemistandardThetaComponentSpace a ha mu d t`, which
  is the conclusion of VII.1.3, surjectivity is equivalent to (1),
  `RationalSemistandardFourierFiniteSupportStatement`, together with (2),
  `UnquotientedReconstructionStatement`. The hypothesis `hsm` stays explicit in the
  theorem. The module does not supply it. In the Library,
  `rationalSemistandardFourierFamily_mem_componentSpace_of_smoothness` gets componentwise
  smoothness from `RationalSemistandardFourierFamilySmoothnessStatement` together with
  existence of `RationalSemistandardFourierAnalyticInputs` (measures on the Levi and
  unipotent radical and the functions `Ξ^M`, `σ^M`) at every full index `t`.

## The linear equivalence

The section variable `hsurj : SynthesisSurjectivityStatement …` is VIII.1.1 for the
fixed data.

- `synthesisLinearEquiv`: under `hinv` and `hsurj`, the complex-linear equivalence
  `rationalSemistandardThetaInvariantSections C ≃ₗ[ℂ] RationalSchwartzSpace hK hPK rho`
  whose underlying map is `κ` (`LinearEquiv.ofBijective`). Injectivity is the VII.2.5
  consequence `SynthesisInverse.invariantSynthesis_injective`; surjectivity is `hsurj`.
- `synthesisLinearEquiv_apply`: the equivalence is `κ`.
- `synthesisLinearEquiv_apply_apply`: its pointwise formula, the weighted source sum of
  VI.3, `κ(ψ)(g) = Σ_(θ ∈ supp ψ) sourceWeight θ · f_(ψ[θ])(g)`
  (`weightedSynthesis_apply`).
- `synthesisLinearEquiv_symm_val`: the inverse is the actual Fourier family: the
  underlying family of `e.symm f` is `psi_f`.
- `synthesisLinearEquiv_symm_eq_fourierInvariantLift`: for any membership witness,
  `e.symm f` is the invariant Fourier lift of `f`.
- `pairing_eq_invariantGlobalForm_symm`: under the VII.2.5 isometry target
  `hiso : SynthesisIsometry.SynthesisIsometryStatement …`, for all Schwartz `f'` and `f`,
  `∫_G conj(f'(g)) f(g) dg = B(psi_f', psi_f)`, where the integral is
  `HarishChandraSchwartz.pairing` for `RationalDynamicSource.ambientHaar K hK` and `B` is
  the source spectral form `GlobalForm.invariantGlobalForm`
  (`SynthesisIsometry.pairing_synthesis_eq_form`).
- `inner_toL2_eq_invariantGlobalForm_symm`: the same identity for the inner product in
  `L²(G)` of the images under the existing inclusion `Space.toL2` built from the `L²`
  weight condition `hsw` (`Space.inner_toL2`).

No topology on `C^∞(Θ)_inv` is introduced, and no continuity or topological
equivalence is asserted.

## Input ledger

- Structural data: as for `κ` and the Fourier family (maximal split torus, generic
  cocharacter, Iwasawa pair, split components and their quotient measures, compact data,
  finite index data, packet data, Weyl comparison data `C`, source height `rho`,
  modular normalization `hdelta`, tempered coefficients `hT`, the `L²` weight `hsw`).
- Normalizations: `IsSourceCompactAt`, `SourceLeviQuotientHaar`, the common compact
  `hd` and `hQ`.
- Density premises of VII.2.5: `DensityNonnegative`, `DensityPositiveDense`.
- Analytic targets taken as hypotheses: VII.2.5 inverse (`hinv`), VII.2.5 isometry
  (`hiso`, only for the form identities), VII.1.4 (`hcov`, only in the covariance
  section), componentwise smoothness (`hsm`, only in the source-form theorem), and
  VIII.1.1 (`hsurj`, in the one-way implications
  `fourierInversion_of_synthesisSurjectivity`,
  `fourierInjectivity_of_synthesisSurjectivity` and
  `unquotientedReconstruction_of_synthesisSurjectivity`, and in the linear equivalence
  and its properties). No equivalence takes `hsurj` as a hypothesis; VIII.1.1 is one
  side of each of them.
- Other conditional input: injectivity of `f ↦ psi_f` (`hinj`, only in
  `synthesisReconstruction_of_fourierInjectivity`).

## Declaration-level dependency map

- `fourierFamily_invariantSynthesis` → `SynthesisInverse.fourier_synthesis`.
- `synthesisSurjectivity_iff_fourierInversion` → `fourierInversion_of_synthesisSurjectivity`,
  `synthesisSurjectivity_of_fourierInversion`.
- `synthesisSurjectivity_iff_lift_and_reconstruction` → `fourierInversionStatement_iff`.
- `synthesisSurjectivity_iff_lift_and_injectivity` →
  `synthesisReconstruction_of_fourierInjectivity`,
  `fourierInjectivity_of_synthesisSurjectivity`.
- `unquotientedReconstruction_of_synthesisSurjectivity` →
  `synthesisReconstruction_iff_unquotiented`.
- `isWeylInvariant_fourierFamily_of_covariance` →
  `rationalSemistandardFourierCovarianceStatement_iff`.
- `synthesisSurjectivity_iff_finiteSupport_and_unquotiented` →
  `synthesisSurjectivity_iff_smoothSections_and_reconstruction`,
  `synthesisReconstruction_of_unquotiented`,
  `unquotientedReconstruction_of_synthesisSurjectivity`.
- `synthesisLinearEquiv` → `SynthesisInverse.invariantSynthesis_injective`.
- `pairing_eq_invariantGlobalForm_symm` → `SynthesisIsometry.pairing_synthesis_eq_form`.
- `inner_toL2_eq_invariantGlobalForm_symm` → `Space.inner_toL2`.
