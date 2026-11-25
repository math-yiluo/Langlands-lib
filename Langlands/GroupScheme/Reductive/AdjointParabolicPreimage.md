# Preimages of parabolic subgroups of the adjoint quotient

This module is part of the proof of
`AdjointParabolicCorrespondenceStatement`. Clause 1 is proved in
`Reductive/ParabolicContainsCenter`, clause 2 in `Reductive/AdjointParabolicImage`,
and clause 4 and the final assembly in `Reductive/AdjointParabolicCorrespondenceProof`.

This module proves clauses 3 and 5 of
`Langlands.GroupScheme.AdjointParabolicCorrespondenceStatement` (Conrad,
*Reductive group schemes* (2014), Exercise 5.5.8). Clause 3 says that the
inverse image of a parabolic subgroup of `G^ad` is parabolic in `G`. Clause 5
says that the correspondence matches Borel subgroups with Borel subgroups. The
proofs are our own route through existing Library results. Over an
algebraically closed field it follows the published
`CentralIsogenyBorelPreimage.isBorelSubgroup_of_range_eq_comap`
(`CentralIsogeny/BorelPreimage.lean`). Over an arbitrary field it follows the
structure of `UnipotentQuotientParabolics` (`Absolute/UnipotentQuotientParabolics.lean`).

All declarations are in namespace
`Langlands.GroupScheme.AdjointParabolicPreimage`. Ranges, comaps and their
equalities are subgroup functors evaluated on every scheme over the base,
including nonreduced tests. `RelativeRoot.IsFppfQuotient (center G) q` means
that `q` is flat, surjective and locally of finite presentation, and the range
of its scheme-theoretic kernel is the centre `center G`.

## Over an algebraically closed field

Here `k` is algebraically closed and all group schemes are over `Spec k`. The
map `π : G ⟶ A` is flat, surjective and locally of finite presentation, with
central kernel `IsCentral (kernelι π)`. The group `G` is connected reductive.
The group `A` is smooth, affine and connected.

### `isBorelSubgroup_of_range_eq_comap`

Let `j : B ⟶ A` be a Borel subgroup and `i : P ⟶ G` a closed subgroup with
`range i = (range j).comap π`. Then `i` is a Borel subgroup.

This generalizes `CentralIsogenyBorelPreimage.isBorelSubgroup_of_range_eq_comap`.
That lemma assumes a central isogeny `π` and a connected reductive `A`. Here `π`
need not be finite, and `A` is only assumed smooth, affine and connected.

Proof. `CentralIsogenyBorelPreimage.exists_isBorelSubgroup_center_le` gives a
Borel subgroup `i₁` of `G` containing the centre. Since the kernel is central,
`i₁` also contains the kernel. `HomImage.exists_image` factors `i₁ ≫ π` as a
flat, surjective, quasi-compact map `p` followed by a closed subgroup `jI` with
smooth connected source. By `CentralIsogenyBorelPreimage.isBorelSubgroup_image`,
`jI` is Borel. By `borelConjugacy`, some rational point `a` of `A` conjugates
`jI` onto `j`. Lift it to a rational point `g` of `G` (`rationalPointLift`), and
let `i₀` be the conjugate of `i₁` by `g`. Then `i₀` is Borel and still contains
the central kernel (`IsCentral.comp_innerIso_hom`). The square
`i₀ ≫ π = p₀ ≫ j` is an fppf image square. So
`SubgroupFunctor.IsFppfImage.comap_eq_of_kernel_le` gives
`(range j).comap π = range i₀`. Hence `range i = range i₀`.
`IsClosedSubgroup.sourceIsoOfRangeEq` then transports the Borel property from
`i₀` to `i`.

### `smooth_of_range_eq_comap`

Let `jJ : J ⟶ A` be a closed subgroup with `J` smooth and connected. Let
`jB : B ⟶ A` be a Borel subgroup with `a ≫ jJ = jB` for some `a : B ⟶ J`. Let
`i : H ⟶ G` be a closed subgroup with `range i = (range jJ).comap π`. Then
`H` is smooth over `Spec k`.

Proof. Let `P := SubgroupPreimage.groupScheme π jJ` be the scheme-theoretic
inverse image. Its projection `r` to `J` is flat and locally of finite
presentation, being a base change of `π`. Let `C` be the reduced identity core
of `P` (`ReducedSubgroup.identityCore`), with inclusion `c` into `G` and map
`s : C ⟶ J`. By `AdjointQuotientBorelImage.surjective_identityCore_comp`, `s`
is surjective. By `HomImage.exists_image`, `s` factors as a flat map followed
by a closed immersion. That closed immersion is surjective onto the reduced
scheme `J`, hence an isomorphism (`isIso_of_isClosedImmersion_of_surjective`).
So `s` is flat and locally of finite presentation.

The inverse image `n` of `jB` is Borel by `isBorelSubgroup_of_range_eq_comap`.
It is smooth and connected, so it factors through the identity core
(`ReducedSubgroup.factorIdentityCore`). Hence `C` contains the kernel of `π`.
`SubgroupFunctor.IsFppfImage.comap_eq_of_kernel_le` gives
`(range jJ).comap π = range c`, so `range i = range c`.
`IsClosedSubgroup.sourceIsoOfRangeEq` gives an isomorphism `H ≅ C` over
`Spec k`. Since `C` is smooth, so is `H`.

## Over an arbitrary field

Here `k` is any field. Let `q : G ⟶ A` satisfy
`RelativeRoot.IsFppfQuotient (center G) q`. The group `G` is connected
reductive, and `A` is smooth, affine and connected. Base change along
`toAlgebraicClosure k` is written `F`, and `k̄` is `AlgebraicClosure k`.

### `isCentral_kernelι_baseChange`

The kernel of `F.map q` is central. Proof: by
`RelativeRoot.IsFppfQuotient.baseChange_center`, `F.map q` is an fppf quotient
by the centre of `F.obj G`. So its kernel's range is that centre
(`isCentral_iff_range_le_center`).

### `isParabolicSubgroup_of_range_eq_comap`

Let `j : P ⟶ A` be a parabolic subgroup and `i : H ⟶ G` a closed subgroup with
`range i = (range j).comap q`. Then `i` is parabolic.

Proof. Over `k̄`, `F.obj G` is connected reductive
(`IsConnectedReductive.baseChange_toAlgebraicClosure`). `F.obj A` and
`F.obj P` are smooth, affine and connected. For `F.obj P`, connectedness comes
from `IsParabolicSubgroup.connectedSpace` and
`connectedSpace_baseChange_of_smooth_affine`. Ranges commute with base change
(`SubgroupFunctor.range_baseChangeHom`, `SubgroupFunctor.comap_baseChange`).
So `range (F.map i) = (range (F.map j)).comap (F.map q)`. Take the Borel
witness `jB`, `a` of `j` over `k̄`.

- Smoothness: `smooth_of_range_eq_comap` over `k̄` shows that `F.obj H` is
  smooth. Smoothness then descends along the fpqc map `Spec k̄ ⟶ Spec k`
  (`fieldExtension_fpqc`, `smooth_of_baseChange`).
- Borel witness: the inverse image `n` of `jB` under `F.map q` is Borel by
  `isBorelSubgroup_of_range_eq_comap`. Its range lies in `range (F.map i)`, so
  `n` factors through `F.map i` (`SubgroupFunctor.exists_factor_of_range_le`).

### `isGeometricBorelSubgroup_iff_of_range_eq_comap`

Let `j : P ⟶ A` and `i : H ⟶ G` be parabolic subgroups with
`range i = (range j).comap q`. Then `IsGeometricBorelSubgroup i` holds if and
only if `IsGeometricBorelSubgroup j` holds.

Proof. Since both sides are represented, the inclusion of ranges gives a
restriction `p : H ⟶ P` with `i ≫ q = p ≫ j`
(`SubgroupFunctor.IsRepresentedBy.restrictionHom`). The square is cartesian
(`IsRepresentedBy.isPullback_of_comap_eq`), so `p` is surjective and locally of
finite presentation. By `IsParabolicSubgroup.isGeometricBorelSubgroup_of_isSolvable`,
a parabolic subgroup is a geometric Borel subgroup once it is solvable. So it
suffices to compare solvability.

- If `i` is Borel, `H` is solvable. Then `P` is solvable as a surjective image
  (`IsSolvableGroupScheme.map_of_surjective`).
- If `j` is Borel, `P` is solvable, and so is `F.obj P`
  (`IsSolvableGroupScheme.baseChange_toAlgebraicClosure`). Over `k̄`,
  `CentralIsogenyBorelPreimage.isSolvable_of_central_kernel` applies to the
  base-changed square, because the kernel of `F.map q` is central. It shows
  that `F.obj H` is solvable. Solvability descends to `H` by
  `IsSolvableGroupScheme.of_baseChange`.

## Over a base scheme

Here `S` is any scheme, `G` is a reductive group scheme over `S`, `Gad` is
affine over `S` (`[IsAffineHom Gad.X.hom]`), and `q : G ⟶ Gad` satisfies
`RelativeRoot.IsFppfQuotient (center G) q`. The affineness of `Gad` is a
hypothesis here. Under these hypotheses `Gad` is reductive
(`RelativeRoot.IsFppfQuotient.isReductive_target`). So for each point `s` of
`S`, the residue fibres `G_s` and `Gad_s` are connected reductive
(`IsReductive.isConnectedReductive_baseChange`). The fibre `q_s` is an fppf
quotient by the centre (`RelativeRoot.IsFppfQuotient.baseChange_center`).

### `isRelativeParabolicSubgroup_preimage`

For a parabolic subgroup `i' : P' ⟶ Gad` over `S`, the scheme-theoretic inverse
image `SubgroupPreimage.inclusion q i'` is a parabolic subgroup of `G` over
`S`.

Proof. `i'` is a closed immersion by `relativeParabolicClosed`. So the inverse
image is a closed subgroup (`SubgroupPreimage.isClosedSubgroup`), hence a
monomorphism, and it is affine over `S` (`SubgroupPreimage.isAffineHom`). Its
residue fibre at `s` is a closed subgroup whose range is the inverse image of
the range of the parabolic `i'_s`. So it is parabolic by
`isParabolicSubgroup_of_range_eq_comap`. For smoothness over `S`: the
projection onto `P'` is a base change of `q`, so it is flat and locally of
finite presentation, and `P'` is smooth over `S`. Hence the inverse image is
flat and locally of finite presentation over `S`. Its fibres are smooth
because they are parabolic. `Smooth.of_smooth_fiberToSpecResidueField` then
concludes.

### `exists_relativeParabolic_preimage`

Clause 3 in the form used by the target statement: for a parabolic subgroup
`i'` of `Gad` there are `P` and a parabolic subgroup `i : P ⟶ G` with
`(range i').comap q = range i`. Take the inverse image above, whose range is
`(range i').comap q` (`SubgroupPreimage.range_inclusion`).

### `isRelativeBorelSubgroup_iff_of_comap_eq`

Clause 5: for parabolic subgroups `i : P ⟶ G` and `i' : P' ⟶ Gad` over `S` with
`(range i').comap q = range i`, `IsRelativeBorelSubgroup i` holds if and only
if `IsRelativeBorelSubgroup i'` holds.

Proof. Both sides are parabolic, so it remains to compare the residue-fibre
conditions `IsGeometricBorelSubgroup`. At each point `s`, the range equality
base-changes to the residue fibres. Then
`isGeometricBorelSubgroup_iff_of_range_eq_comap` applies.
