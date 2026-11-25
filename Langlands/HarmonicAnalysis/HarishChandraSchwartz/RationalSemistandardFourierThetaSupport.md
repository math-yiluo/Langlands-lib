# Support of the actual Fourier family in `Theta^H` (Waldspurger VIII.1.3)

This module applies the fixed-level support interfaces to the actual full
Fourier family `psi_f`, which is `rationalSemistandardFourierFamily` on the
full intrinsic index `RationalSemistandardTheta a ha muM`. It contains:

- a proof of the support inclusion of Remark VIII.1.3;
- exact Prop targets for the full and proper forms of VIII.1.3(ii), with
  their conditional deductions from finiteness of `Theta^H`;
- the finite-support and proper-supported restrictions of `psi_f` into
  `C^infinity(Theta)`, with their laws;
- the comparison with the existing standard constructions.

No finiteness of `Theta^H` and no smoothness of `psi_f` is assumed or proved
here except through explicit premises.

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques
(d'après Harish-Chandra)*, J. Inst. Math. Jussieu 2 (2003), printed p.321
(PDF p.87), registered as `waldspurger-2003-plancherel`.

- VIII.1, definition of `Theta^H`: `(O,P) ∈ Theta^H` when `I_P^G E` has a
  nonzero `H`-fixed vector for some `(omega,E) ∈ O`.
- Remark VIII.1.3(ii): for `f ∈ C(G)`, the set of `(O,P) ∈ Theta`, resp.
  `Theta - Theta_G`, with `psi_f[O,P] ≠ 0` is finite.
- The proof after the remark: if `f` is bi-invariant under a compact open `H`,
  then `psi_f[O,P] ≠ 0` only if `(O,P) ∈ Theta^H`. So (ii) follows from (i),
  the finiteness of `Theta^H`, resp. `Theta^H - Theta^H_G`.
- VIII.2, printed p.321: `psi` equals `psi_f` off `Theta_G` and `0` on
  `Theta_G`. Only this shape is used here, through the proper-supported family.

## Imported interfaces

- From `RationalSemistandardFourierTransform` and
  `RationalSemistandardFourierFamily`: `rationalSemistandardFourierFamily`, its
  evaluation lemma `rationalSemistandardFourierFamily_apply`,
  `rationalSemistandardInducedFourierTransform_eq_inducedFourierTransform`, the
  smoothness target `RationalSemistandardFourierFamilySmoothnessStatement` with
  `RationalSemistandardFourierAnalyticInputs`, the standard comparison target
  `RationalSemistandardFourierStandardComparisonStatement` and its normalization
  `RationalSemistandardStandardFourierNormalization`.
- From `RationalSemistandardThetaFixed`, `RationalSemistandardThetaParts` and
  `RationalSemistandardThetaFixedSupport`:
  `rationalSemistandardThetaFixed` (`Theta^H`),
  `rationalSemistandardThetaProper`, the proper part and proper restriction, the
  conditional constructors of `RationalSemistandardThetaParts`, and the
  submodules `rationalSemistandardThetaFixedSupported`,
  `rationalSemistandardThetaProperFixedSupported` with their finite-index
  deductions from `RationalSemistandardThetaFixedSupport`.
- Published: `inducedFourierTransform_eq_zero_of_fixedVectors_eq_bot` and
  `mk_mem_inducedDiscreteSeriesFixedOrbits_of_representative`
  (`RationalInducedFixedOrbits`), `mk_discreteSeriesClass_orbitRepresentative`
  (`RationalSemistandardOrbitSections`), `Space.exists_isBiInvariant`,
  `rationalStandardFullRestrict` and `rationalStandardFullSmoothRestrict`
  (`RationalSemistandardStandardComparison`), and `rationalFourierThetaFamily`
  (`RationalStandardSpectralFamily`).

The variables are those of the full-product section of
`RationalSemistandardFourierFamily`: `hG hi hnu hKc hPK rho hsw` for the group,
the Schwartz space and its weights, then `a ha muM d hdelta hT` for the split
components, quotient Haar measures, compact data, modular normalizations and
induced temperedness. Two local instances supply a compact open subgroup of
`G(F)` and the local compactness of each actual parabolic, as in that module.

## The support inclusion (closed target, proved)

- `rationalSemistandardFourierFamily_apply_eq_zero_of_not_mem_thetaFixed`: if
  `f` is right invariant under a subgroup `H` and `t ∉ Theta^H`, then
  `psi_f[t] = 0`.
  Proof: each value `psi_f[t](A)` at a member `A` of the unitary unramified
  orbit is, by the evaluation lemma `rationalSemistandardFourierFamily_apply`, the published induced Fourier
  transform at `A`. The published `inducedFourierTransform_eq_zero_of_fixedVectors_eq_bot`
  (Lemma VII.1.1(i)) makes it vanish once `I_P^G A` has no nonzero `H`-fixed
  vector. If `I_P^G A` had one, `mk_mem_inducedDiscreteSeriesFixedOrbits_of_representative`
  would put the orbit of the chosen representative into `Theta^H`. By
  `mk_discreteSeriesClass_orbitRepresentative` that orbit is `t.2`, which
  contradicts `t ∉ Theta^H`. No comparison target is needed.
- `rationalSemistandardFourierFamily_mem_thetaFixedSupported`: for right
  `H`-invariant `f`, `psi_f` lies in `rationalSemistandardThetaFixedSupported H`.
- `RationalSemistandardFourierThetaFixedSupportStatement`: the source form, a
  Prop. For every subgroup `H` that is open and compact and every `f` that is
  bi-invariant under `H` (`IsBiInvariant H f`), `psi_f` is supported in
  `Theta^H`.
- `rationalSemistandardFourierThetaFixedSupportStatement_holds` proves it. Only
  right invariance is used, obtained from bi-invariance with left factor `1`.
- `rationalSemistandardFourierFamily_mem_thetaProperFixedSupported` gives the
  proper form: `support psi_f ∩ Theta_proper ⊆ Theta^H`.

## VIII.1.3(ii) for `psi_f` (targets and conditional deductions)

- `RationalSemistandardFourierFiniteSupportStatement`: for every `f`, the
  support of `psi_f` is finite (full VIII.1.3(ii)).
- `RationalProperSemistandardFourierFiniteSupportStatement`: for every `f`,
  `support psi_f ∩ Theta_proper` is finite (proper VIII.1.3(ii)). Nothing is
  required at `P = G`.
- `rationalSemistandardFourierFiniteSupport_of_support_of_fixedFinite` deduces
  the full statement from two premises: the support target, and finiteness of
  `Theta^H` for every open compact subgroup `H`, the conclusion of full
  VIII.1.3(i). It picks a compact open `H` under which `f` is bi-invariant
  (`Space.exists_isBiInvariant`) and applies the finite-index step.
- `rationalProperSemistandardFourierFiniteSupport_of_support_of_fixedFinite`
  does the same from the support target and finiteness of
  `Theta^H ∩ Theta_proper` only, the conclusion of proper VIII.1.3(i).
  Finiteness of the full `Theta^H` is not used.
- `rationalSemistandardFourierFiniteSupport_of_fixedFinite` and
  `rationalProperSemistandardFourierFiniteSupport_of_fixedFinite` discharge the
  support premise with the proof above. The finite-index premise stays
  explicit.
- `RationalSemistandardFourierFiniteSupportStatement.proper`: the full statement
  implies the proper one.

The finite-index premises are stated literally as finiteness of
`rationalSemistandardThetaFixed a ha muM H`, resp. of its intersection with
`rationalSemistandardThetaProper a ha muM`, for every open compact `H`. The
conditional VIII.1.3(i) adapters of `RationalSemistandardThetaFixedFiniteness`
produce exactly these sets.

## Componentwise smoothness

`rationalSemistandardFourierFamily_mem_componentSpace_of_smoothness` puts every
component of `psi_f` in its coherent smooth space. It takes
`RationalSemistandardFourierFamilySmoothnessStatement` and, at every index,
some Haar measures and weights satisfying `RationalSemistandardFourierAnalyticInputs`.
It gives the premise `hsm` used below. The smoothness itself is not proved.

## Finite-support and proper-supported restrictions

The raw family `psi_f` is a product. It enters `C^infinity(Theta)` only through
the following constructors, which take a support proof.

- `rationalSemistandardFourierThetaSmoothFamily hsm hfs` is the complex-linear
  map `C(G) → C^infinity(Theta)`. It takes componentwise smoothness `hsm` and
  the full finite-support statement `hfs`. Its value is `psi_f` (`_val`).
- `rationalSemistandardFourierThetaProperSmoothFamily hsm hfs` takes smoothness
  only at proper indices and the proper finite-support statement. It is the
  complex-linear map whose value is the proper part of `psi_f`, equal to
  `psi_f` at `P ≠ G` and `0` at `P = G` (`_val`). This is the shape of VIII.2's
  `psi`. Full finite support is not required. Membership in the invariant
  subspace `C^infinity(Theta)^inv` is not claimed: support carries no
  covariance.
- `rationalSemistandardFourierProperSmoothFamily hsm hfs` takes the same inputs.
  It is the complex-linear map into finitely supported smooth families on the
  proper index type `Theta - Theta_G`, with value the proper restriction of
  `psi_f` (`_val`).
- `rationalSemistandardThetaSmoothProperPart_fourierThetaSmoothFamily`: under
  the full hypotheses, the smooth proper part of the full map is the
  proper-supported map. Its premises are those induced from the full ones.
- `rationalSemistandardProperSmoothRestrict_fourierThetaProperSmoothFamily`:
  restricting the proper-supported map to the proper index type gives the
  proper-index map.

Linearity comes from the linearity of `psi_f`, the proper part and the proper
restriction. The constructors are the conditional constructors of
`RationalSemistandardThetaParts`.

## Standard slice

The variables `b hb eta` and the published discrete-series comparison `hds`
are those of `RationalSemistandardStandardComparison`. The restrictions use
Borel compatibility for both quotient measurable structures at each standard
index. The full Fourier family already supplies this compatibility for its
semistandard quotient data.

- `rationalStandardFullRestrict_fourierFamily_support_subset_rationalThetaFixed`
  holds for right `H`-invariant `f`. The nonzero components of the
  restriction of `psi_f` to the existing standard product have indices in the
  existing standard `rationalThetaFixed H`. The theorem
  combines the support inclusion with
  `rationalStandardFullRestrict_support_subset_rationalThetaFixed`.
- `rationalStandardFullSmoothRestrict_fourierThetaSmoothFamily_val`: restricting
  the finite-support family with the published `rationalStandardFullSmoothRestrict`
  gives the existing standard family `rationalFourierThetaFamily f`. The
  restriction keeps its own model-smoothness comparison premise `hsmc`. The
  result is conditional on the standard comparison target of
  `RationalSemistandardFourierFamily` and its normalization, which are explicit premises. The standard hypotheses `hrho`,
  `hKrho`, `hM` and `hTA` are those of the existing standard family and are not
  strengthened.

## Provenance

The support inclusion, the two VIII.1.3(ii) targets and their deduction from
VIII.1.3(i) transcribe the remark and the argument after it on printed p.321.
The vanishing argument is the source's "il est clair", made precise through
Lemma VII.1.1(i) in the published induced transform. The linear maps, the
proper-supported shape and the standard comparisons are derived interfaces.
They use the imported constructors and support laws.
