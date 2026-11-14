# Unipotence of the special-fibre kernel between unramified parahoric models

Module `Langlands.BruhatTits.IntegralModels.UnramifiedModelKernelTorus`.

## Purpose and provenance

This module specializes the torus argument of
`Langlands.GroupScheme.IntegralModel.SpecialFibreKernelTorus` to the setting of
Kaletha–Prasad, *Bruhat–Tits theory: a new approach* (2023), Proposition 8.4.15
(printed pp. 306–307, PDF pp. 337–338). The host statement is
`UnramifiedModelKernelStatement` (Task 5901). Its unipotence part is proved here
under the assumption that the kernel is smooth and connected. The remaining
smoothness and connectedness are packaged as an internal reduction target.

The statements and their arrangement are internal design by Worker 4783 for
Task 6203, which Worker 282 and Worker 4783 share. The definition
`UnramifiedCompatibleModelKernelSmoothConnectedStatement` is an internal
reduction target, not a statement from the literature. This module does not
prove `UnramifiedModelKernelStatement`.

Notation: `F` is a nonarchimedean local field, `K = inertiaFixedField F` its
maximal unramified extension with integers `fixedFieldIntegers F`, and
`MaximalUnramified.valuation F` the normalized valuation of `K`. `H` is an
affine group scheme over `K`. `C : MaximalUnramified.BuildingData F H` supplies
a maximal split torus `C.i : C.S.toGrp ⟶ H`, the apartment `C.Apartment`, its
map `C.apartmentMap` to the reduced building, and the pointwise fixers
`C.pointwiseFixer`. `E : UnramifiedZeroDatum F H` supplies the subgroup
`E.zeroPoints`, which is KP's `G(K)^0`.

## Results

* `map_characterValuationKernel_le_zeroPoints_inf_pointwiseFixer`: for every
  subset `Ω` of the apartment, the image under `C.i` of the character valuation
  kernel `S(K)^1 = characterValuationKernel (MaximalUnramified.valuation F)
  C.S.toGrp` lies in `E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ω)`.

  *Proof.* The zero-points part is the published
  `UnramifiedZeroDatum.map_split_characterValuationKernel_le_zeroPoints`, applied
  to the split subtorus `C.i`. For the fixer part, the published
  `KPApartmentData.map_torusUnits_smul_apartmentMap` (with the identity of
  `C.S`) uses axiom V 6 (`C.isOmegaCompatible`): every point of `S(K)^1` fixes
  every point `C.apartmentMap x`.
* `isUnipotent_kernel_specialFibreMap_of_apartment`: let `Ω` and `Ω'` be subsets
  of the apartment. Let `N` and `N'` be models of `H` over the integers of `K`,
  with `N'` smooth, such that
  `E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ω) ≤ N.integralPoints` and
  `E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ω') ≤ N'.integralPoints`.
  Let `ψ : N'.Hom N (𝟙 H)`. If `kernel ψ.specialFibreMap` is smooth and
  connected (instances), it is unipotent.

  *Proof.* The integers of `K` form a Henselian discrete valuation ring with
  algebraically closed residue field. The published inputs are
  `fixedFieldIntegersIsHenselian`, `fixedFieldIntegersIsDVR_of_valuesFromBase`
  with `fixedFieldValuesFromBase`, and `fixedFieldResidueIsAlgClosure`. The
  valuation is one on their units
  (`SpecialTorusIntegralModel.valuation_units_eq_one`). By the previous result,
  `S(K)^1` lies in the integral points of both models. Apply
  `IntegralModel.isUnipotent_kernel_specialFibreMap_of_bounded` to the maximal
  split torus `C.i`, using `C.isConnectedReductive`.
* `UnramifiedCompatibleModelKernelSmoothConnectedStatement`: the part of the
  reduction target `UnramifiedCompatibleModelKernelStatement` (module
  `Langlands.BruhatTits.IntegralModels.UnramifiedModelKernelReduction`, approved
  candidate `3c8c7c2b`, not yet integrated) that
  asserts only that `kernel ψ.specialFibreMap` is smooth and connected. Its
  hypotheses are exactly those of `UnramifiedCompatibleModelKernelStatement`:
  * `G` is an affine group over `F`, with base change `G_K` to `K`;
  * `C` is building data of `G_K`;
  * `E` is a zero datum whose torus represents the centralizer of `C.i`;
  * `Ωa` and `Ωa'` are subsets of the apartment, `Ωa` nonempty, `Ωa'` bounded
    for every real affine functional, and `Ωa` contained in the closure of
    `Ωa'` for the topology induced by the real affine functionals;
  * `N` and `N'` are smooth models of `G_K` over the integers of `K` with
    integral points `E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ωa)` and
    `E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ωa')`;
  * `ψ : N'.Hom N (𝟙 _)`.
* `unramifiedCompatibleModelKernel_of_smoothConnected`: the smooth-connected
  statement implies `UnramifiedCompatibleModelKernelStatement`. Unipotence comes
  from `isUnipotent_kernel_specialFibreMap_of_apartment`. Here the equalities of
  integral points are used only as inclusions, and nonemptiness, boundedness,
  closure and compatibility are not used.
* `unramifiedModelKernel_of_smoothConnected`: given
  `UnramifiedQuasiSplitStatement` and `UnramifiedZeroPointsIndependenceStatement`,
  the smooth-connected statement implies `UnramifiedModelKernelStatement`. This
  composes the previous result with
  `unramifiedModelKernel_of_compatible` (same module). All three hypotheses are unproved
  statements, so this theorem does not prove the host statement.

## Implementation notes

The theorem `unramifiedCompatibleModelKernel_of_smoothConnected` uses
`maxHeartbeats 1600000`, like `unramifiedModelKernel_of_compatible`, because
elaborating the long universally quantified statements is expensive. A private
instance supplies `IsAffineHom` for the base change of `G` to `K`; it is the
same as the private instance of the statement module.
