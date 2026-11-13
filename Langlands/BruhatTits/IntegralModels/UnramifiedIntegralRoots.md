# Integral apartment tori and root models in a full unramified fixer model

This derived unit constructs the integral split torus and root-filtration
models inside a supplied full one-fixer integral model. It uses the exact
`MaximalUnramified.BuildingData` of the parahoric-model target, with no extra
apartment axioms or local-field structure on the inertia fixed field.

First work over a noetherian valuation domain `R : Type u` with infinite
residue field and specified fraction field `K : Type u`. Let `v` be an
integer-valued valuation of `K`, let `C : IntegerValuationBuildingData v G`,
and let `N : IntegralModel R K G`. Suppose `v` is one on all units of `R`
and suppose

`N.integralPoints = characterValuationKernel v G ∩
C.pointwiseFixer (C.apartmentMap '' Ω)`.

`map_apartmentTorus_characterValuationKernel_le_oneFixer` proves that the
image of the apartment torus's character-valuation kernel lies in this
one-fixer, for every apartment subset `Ω`. The character-kernel inclusion
is functorial. Fixation uses the published full V6 centralizer compatibility
and scalar torus unit theorem, applied to the identity of `C.S`.

`exists_integralSplitTorusData_of_oneFixer` applies the published
`SplitTorusClosure.exists_isSplitTorus_genericTorusMap_eq_of_bounded` to
that inclusion. This supplies an actual integral split torus, a closed map
into `N.group`, its generic identification with the prescribed `C.S`,
and the commuting square with the actual generic inclusion `C.i`.
The result is packaged in `IntegralSplitTorusData`, together with proof
that its integral map is closed. Smoothness of `N` is not needed here.

Now let `F` be a nonarchimedean local field, `K = inertiaFixedField F`,
`R = fixedFieldIntegers F`, and `v = MaximalUnramified.valuation F`.
`exists_unramifiedIntegralSplitTorusData` verifies all additional ring
conditions from existing arithmetic. The value-attainment theorem gives
that `R` is a discrete valuation ring. Its residue field is an algebraic
closure of the residue field of `F`, hence infinite. The normalized
valuation is equivalent to the defining valuation of `R`, so it has value
one on every unit. Thus a supplied full one-fixer model contains the
required actual closed integral split torus.
`unramifiedIntegralSplitTorusData` chooses it, and
`unramifiedIntegralSplitTorusData_isClosedSubgroup` records its closed map.

If `N` is smooth, `Ω` is nonempty and bounded above under every real
affine functional, `unramifiedRootFiltrationModelData` constructs, for
each relative root `a` and reference point `x`, the actual
`RootFiltrationModelData` at
`C.apartment.rootFixerDepth a x Ω`. This includes the full all-test
generic root representative, smooth affine integral model,
geometrically connected fibres and exact filtration point image.
`unramifiedRootFiltrationModelMap` gives the actual compatible map to `N`;
`unramifiedRootFiltrationModelMap_isClosedSubgroup` proves it is closed.
These declarations apply `IntegralRootFiltration` to the constructed
torus. They require no supplied integral torus or root-filtration image
identity.

The provenance is internal: the construction composes published bounded
split-torus extension, torus-unit fixation, actual maximal-unramified
arithmetic and the integral root-filtration construction. The full ambient
integral model and its one-fixer point equality remain supplied. The unit
constructs no full ambient model, no maximal torus Iwahori model, no
zero-subgroup comparison and no final parahoric-model proof.
