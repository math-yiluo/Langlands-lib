# Support at a fixed level and the conditional VIII.1.3(ii) adapters

This module handles the finite-index step of Waldspurger's Remark
VIII.1.3(ii), for an arbitrary raw family on the full intrinsic index
`RationalSemistandardTheta a ha mu`. It defines families supported in `Theta^H`,
deduces finite support from finiteness of `Theta^H`, and builds the
corresponding maps into the direct sum `C^infinity(Theta)`. There is a full
variant and a proper variant (`P ≠ G`).

The module does not refer to the Fourier family `psi_f`. The source's support
inclusion (`psi_f[O,P] ≠ 0` only if `(O,P) ∈ Theta^H` when `f` is
`H`-bi-invariant) concerns `psi_f` and is not stated here. Applied to
`psi_f`, the results below give VIII.1.3(ii) once that inclusion is known.
No finiteness is assumed or concluded except through explicit premises.

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques
(d'après Harish-Chandra)*, J. Inst. Math. Jussieu 2 (2003), printed p.321
(PDF p.87), registered as `waldspurger-2003-plancherel`.

- Remark VIII.1.3(ii): for every `f ∈ C(G)`, the set of `(O,P) ∈ Theta`, resp.
  `Theta - Theta_G`, with `psi_f[O,P] ≠ 0` is finite.
- The proof after the remark: if `f` is bi-invariant under a compact open `H`,
  then `psi_f[O,P] ≠ 0` only if `(O,P) ∈ Theta^H`. So (ii) follows from (i):
  finiteness of `Theta^H`, resp. `Theta^H - Theta^H_G`.

This module formalizes the last deduction, which is a set inclusion, for any
family.

## Imported interfaces

- `rationalSemistandardThetaFixed a ha mu H` (`Theta^H`) and its antitonicity,
  from `RationalSemistandardThetaFixed`.
- `rationalSemistandardThetaProper`, `rationalSemistandardThetaProperPart` and
  the conditional constructors from `RationalSemistandardThetaParts`.
- `finite_rationalSemistandardThetaFixed` and
  `finite_rationalProperSemistandardThetaFixed` (the full and proper
  VIII.1.3(i) adapters) from `RationalSemistandardThetaFixedFiniteness`.
- `rationalSemistandardThetaFixed_standard_preimage` from
  `RationalSemistandardThetaFixedStandardComparison`, and
  `rationalStandardFullRestrict_support` from the published
  `RationalSemistandardStandardComparison`.

## Families supported in `Theta^H`

- `rationalSemistandardThetaFixedSupported a ha mu H` is the complex submodule
  of full families `f` with `support f ⊆ Theta^H`. The lemmas
  `mem_rationalSemistandardThetaFixedSupported` and `..._iff_forall` unfold it.
  The second form says that `f t ≠ 0` implies `t ∈ Theta^H`.
- `rationalSemistandardThetaProperFixedSupported a ha mu H` is the submodule of
  `f` with `support f ∩ Theta_proper ⊆ Theta^H`. It requires nothing at
  `P = G`. By `..._iff_properPart`, `f` lies in it iff the proper part of `f`
  (extension by zero across `P = G`) lies in the full submodule.
- `rationalSemistandardThetaFixedSupported_le_proper`: the full condition implies
  the proper one.
- Both submodules are antitone in `H`, because `Theta^H` grows when `H` shrinks.

## The finite-index step

- `finite_rationalSemistandardThetaSupport_of_fixedSupported`: if
  `support f ⊆ Theta^H` and `Theta^H` is finite, then `support f` is finite.
- `finite_rationalSemistandardThetaSupport_inter_proper_of_properFixedSupported`:
  if `support f ∩ Theta_proper ⊆ Theta^H` and `Theta^H ∩ Theta_proper` is finite,
  then `support f ∩ Theta_proper` is finite. Finiteness of the full `Theta^H` is
  not used.
- `..._of_fixedSupported_of_local` and
  `..._inter_proper_of_properFixedSupported_of_local` supply the finiteness of
  `Theta^H` from the VIII.1.3(i) adapters for a compact open `H`. They keep all
  of the adapters' premises explicit: compactness of `K`, finiteness of the
  set of semistandard indices, the normal-level fixed-vector comparison, and
  local VIII.1.2 for the Levis. In the proper version the comparison and local
  VIII.1.2 are needed only for proper parabolics and proper Levis. These two
  theorems carry the Borel-space instances that the adapters use.

## Smooth families at a fixed level and maps into `C^infinity(Theta)`

`d` is a choice of compact data at every index, as in
`rationalSemistandardThetaSmoothSections a ha mu d`.

- `rationalSemistandardThetaFixedSmooth a ha mu d H` is the submodule of
  families with every component in its coherent smooth component space and
  support in `Theta^H`. Finiteness is not part of the definition.
- `rationalSemistandardThetaProperFixedSmooth a ha mu d H` requires smooth
  components only at proper indices and only proper support in `Theta^H`.
- `..._le_proper` and `..._antitone` relate these submodules as above.
- `rationalSemistandardThetaSmoothOfFixed d hfin` takes `hfin`, finiteness of
  `Theta^H`, and gives the complex-linear inclusion of the full fixed-level
  smooth submodule into `C^infinity(Theta)`. Its value is the family itself
  (`_val`). By `rationalSemistandardThetaSmoothOfFixed_of_le`, it does not
  depend on the level that certified finiteness.
- `rationalSemistandardThetaProperSmoothOfFixed d hfin` takes only finiteness of
  `Theta^H ∩ Theta_proper`. It is the complex-linear map from the proper
  fixed-level smooth submodule into `C^infinity(Theta)` whose value is the proper
  part of the family, with zero at `P = G` (`_val`). This is the shape of
  VIII.2's `psi`. VIII.2's further membership `psi ∈ C^infinity(Theta)^inv` is
  not claimed: support carries no covariance.
- `rationalSemistandardProperSmoothOfFixed d hfin` takes the same inputs and
  gives the finitely supported family on the proper index type. Its value is
  the proper restriction (`_val`).
- `rationalSemistandardProperSmoothRestrict_properSmoothOfFixed`: restricting the
  proper-supported family to the proper index type gives the proper-index
  family.
- `rationalSemistandardThetaSmoothProperPart_smoothOfFixed`: if the full
  `Theta^H` is finite, the smooth proper part of the full map equals the proper
  map. That map is certified by the induced finiteness of the proper part.

All three maps are the conditional constructors of `RationalSemistandardThetaParts`
with the finite-support argument discharged by the finite-index step.

## Standard slice

`rationalStandardFullRestrict_support_subset_rationalThetaFixed` uses the
published discrete-series comparison `hds` with Borel compatibility for
both quotient measurable structures at each standard index. If `f` is
supported in the full `Theta^H`, then the nonzero components of
`rationalStandardFullRestrict f` have indices in the existing standard
`rationalThetaFixed H`. The proof combines the published support formula for
the restriction with the preimage identity of the fixed sets.

## Provenance

The finite-index step transcribes the deduction of VIII.1.3(ii) from (i) in the
source. The submodules, linear maps and comparison laws are derived interfaces
for that deduction. Their proofs use set inclusions, the support laws of
`RationalSemistandardSpectralFamily` and `RationalSemistandardThetaParts`, the
antitonicity of `Theta^H`, and the imported adapters.
