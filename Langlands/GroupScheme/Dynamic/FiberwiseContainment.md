# Dynamic parabolic containment detected on residue fibres

Worker 606.

This is an internal, derived ingredient for the proof of
`Langlands.GroupScheme.RelativeParabolicLieContainmentStatement`. It combines
published dynamic representability and smoothness with the fibrewise criterion
for open immersions. It does not assert a new translation of a numbered
literature result.

## Containment homomorphism

`Dynamic.parabolicContainmentHomOfResidueFibres` constructs a group-scheme
homomorphism `H → K` for specified representatives `i : H → G` of `P(χ)` and
`j : K → G` of `P(χ′)`, under the smoothness, affineness and residue-fibre
hypotheses below. The construction applies `hj.liftOfLE` to `i`, after obtaining
global containment from `parabolic_le_of_residueFibres`.
`parabolicContainmentHomOfResidueFibres_comp` proves that its composite with `j`
is `i`. This is actual morphism data, rather than a new proposition target.

## Statements and hypotheses

`Langlands.GroupScheme.Dynamic.parabolic_le_of_residueFibres` applies over any
scheme `S`, with a smooth affine group scheme `G` and two cocharacters `χ, χ'`.
It assumes that the functorial range of `χ'` is contained in `P_G(χ)`. If
`P(χ_s) ≤ P(χ'_s)` as subgroup functors on every residue-field fibre of `S`,
then `P_G(χ) ≤ P_G(χ')` as subgroup functors over `S`.

`Dynamic.parabolic_le_of_fieldBaseChange` has the same conclusion and assumes
containment after every field-valued base change. It specializes that
hypothesis to residue fields and invokes the first theorem.

No connectedness or reductivity hypothesis is needed. The assumption on the
range of `χ'` provides a cocharacter of `P_G(χ)`; this makes its dynamic
intersection with `P_G(χ')` smooth over the base. This proof does not detect
containment of arbitrary smooth subgroups merely from fibrewise containment.

## Proof

Represent `P_G(χ)` by a closed subgroup `i : H → G`, using
`dynamicBaseRepresentability`. The group `H` is smooth over `S` by
`dynamicBaseSmoothConnected` and affine because `i` is closed and `G` is affine.
Lift `χ'` to a cocharacter `χH` of `H` using
`SubgroupFunctor.IsRepresentedBy.liftOfLE`. Closed-subgroup compatibility gives
`P_H(χH) = i⁻¹(P_G(χ'))`.

Represent `P_H(χH)` by `κ : K → H`. Again `K` is smooth over `S`. On each
residue fibre, the assumed containment implies that the functorial range of
`κ_s` is all of `H_s`: the image under `i_s` of every test point of `H_s`
belongs to `P(χ_s)`, hence to `P(χ'_s)`. The monomorphism `κ_s` is therefore
an isomorphism.

The helper `DynamicContainment.isIso_of_residueFibres` shows that `κ` is an
isomorphism on underlying schemes. Smoothness of `K` supplies flatness and local
finite presentation over `S`; smoothness of `H` supplies local finite type.
The published theorem
`Langlands.AlgebraicGeometry.isOpenImmersion_of_fiberwise` therefore makes `κ`
an open immersion. Surjectivity follows by lifting each target point to the
residue fibre above its image in `S` and using surjectivity of `κ_s`.
An open immersion that is surjective is an isomorphism.

Finally every point of `H` lifts along `κ`, so it lies in `P_H(χH)`.
Mapping it along `i` proves the required functorial containment.

The auxiliary helper `DynamicContainment.isIso_of_range_eq_top` handles the
fibre step: evaluate the full-range condition at the identity point of the
target to obtain a section; a monomorphism with a section is an isomorphism.
Its conclusion concerns the morphism in `Over S`.

## Published dependencies

- `Langlands.GroupScheme.dynamicBaseRepresentability`, in
  `Dynamic.BaseRepresentabilityProof`.
- `Langlands.GroupScheme.dynamicBaseSmoothConnected`, in
  `Dynamic.BaseSmoothConnectedProof`.
- `SubgroupFunctor.IsRepresentedBy.liftOfLE` and `liftOfLE_comp`, in
  `Dynamic.ParabolicLieCriterion`.
- `Dynamic.parabolic_eq_comap_of_isClosedSubgroup`, in
  `Dynamic.ClosedSubgroup`.
- `Dynamic.parabolic_baseChange`, in `Dynamic.BaseChange`, and
  `SubgroupFunctor.IsRepresentedBy.baseChange` and `range_baseChangeHom`, in
  `SubgroupBaseChange`.
- `Langlands.AlgebraicGeometry.isOpenImmersion_of_fiberwise`, in
  `Langlands.AlgebraicGeometry.FiberwiseOpenImmersion`.
- Mathlib's pullback point lifting, the mono and split-epi isomorphism
  criterion, and `isIso_iff_isOpenImmersion_and_surjective`.
