# Closed split tori of integral models from bounded points

This module restates the closure theorem
`exists_isClosedSubgroup_genericTorusMap_eq` of
`Langlands.GroupScheme.IntegralModel.SplitTorusUnitPoints` in terms of the
character valuation kernel `characterValuationKernel v T` of
`Langlands.Geometry.Building.KPZeroSubgroups`. That kernel is the subgroup of
rational points `g` of `T` with `v (χ g) = 1` for every rational character
`χ` of `T`. The hypothesis of the closure theorem asks that the unit points of
`𝔾_m^I` be integral. Here it is replaced by: the image of the character
valuation kernel of a split torus lies in the integral points of the model.

All rings live in one universe `u`. The declarations live in the namespace
`Langlands.GroupScheme.IntegralModel.SplitTorusClosure`.

## Split coordinates

`affinePointsEquiv_eq_of_left_eq`: let `S` be a scheme, `I` a finite type,
`A` a commutative ring and `f₁ f₂ : Spec A ⟶ S`. Take points
`x : Over.mk f₁ ⟶ (splitTorus S I).X` and `y : Over.mk f₂ ⟶ (splitTorus S I).X`
with the same underlying scheme morphism. Then their affine split coordinates
`splitTorus.affinePointsEquiv I f₁ x` and `splitTorus.affinePointsEquiv I f₂ y`
agree. This follows coordinatewise from `affinePointsEquiv_val` and
`pointsEquiv_eq_of_left_eq`.

## Unit points in the character valuation kernel

Let `k` and `L` be fields with `L` a `k`-algebra, and `I` a type.

* `rationalCoeffEquiv_symm_algebraPointsEquiv_symm` (`I` finite): for
  `t : I → kˣ`, the `k`-point `(splitTorus.algebraPointsEquiv I k).symm t`
  of `𝔾_m^I` over `Spec k`, read as a rational point through
  `(rationalCoeffEquiv k _).symm`, is the rational point
  `(splitTorus.affinePointsEquiv I (𝟙 _)).symm t`. Both points have
  coordinates `t`. Their underlying scheme morphisms agree by
  `rationalCoeffEquiv_left`, so `affinePointsEquiv_eq_of_left_eq` applies.
* `baseChangeCoeffEquiv_symm_algebraPointsEquiv_symm` (`I` finite): for
  `t : I → Lˣ`, the `L`-point `(splitTorus.algebraPointsEquiv I L).symm t`
  of `𝔾_m^I` over `Spec k`, read as a rational point of the base change to
  `L` through `(baseChangeCoeffEquiv k L _).symm`, is the image under
  `(splitTorus.baseChangeIso (baseMap k L) I).inv` of the rational point of
  `𝔾_m^I` over `Spec L` with coordinates `t`. The proof compares coordinates.
  The published `splitTorus.affinePointsEquiv_baseChangeIso_inv` computes the
  coordinates of the right side. The underlying morphisms are matched by
  `baseChangeCoeffEquiv_left` and `GroupScheme.baseChangePointsEquiv_left`.
* `rationalCoeffEquiv_symm_mem_characterValuationKernel` (`I` a fintype): let
  `v` be a valuation on `k` and `t : I → kˣ` with `v (t i) = 1` for all `i`.
  Then the rational point of the first item lies in
  `characterValuationKernel v (splitTorus (Spec k) I)`. This is the published
  `mem_split_characterValuationKernel`.
* `baseChangeCoeffEquiv_symm_mem_characterValuationKernel` (`I` a fintype):
  let `v` be a valuation on `L` and `t : I → Lˣ` with `v (t i) = 1` for all
  `i`. Then the rational point of the second item lies in the character
  valuation kernel of the base change of `𝔾_m^I` to `L`. By the second item it
  is the image of a point of the kernel for `𝔾_m^I` over `L`
  (`mem_split_characterValuationKernel`). Homomorphisms map character
  valuation kernels into character valuation kernels
  (`map_characterValuationKernel_le`).

## Isomorphisms of commutative group schemes

`commIsoOfGroupIso e`: an isomorphism `e : T.toGrp ≅ T'.toGrp` of the
underlying group schemes of two commutative group schemes over `S`, viewed as
an isomorphism `T ≅ T'` of commutative group schemes.
`groupHom_commIsoOfGroupIso_hom` records that its underlying group
homomorphism is `e.hom` (by definition).

## Closed split tori

Let `R` be a commutative ring with fraction field `K`, `G` a group scheme over
`Spec K` and `M : IntegralModel R K G`.

* `isSplitTorus_torus` (`I` a fintype with decidable equality): `torus R I`,
  that is `D_R(ℤ^I)`, is a split torus, through `splitIsoR R I`.
* `mem_baseChange_self_coefficientIntegralPoints_iff` (`R` a domain): a
  `K`-point `p` of `G` lies in
  `(M.baseChange R K).coefficientIntegralPoints K K` exactly when the rational
  point `(rationalCoeffEquiv K G).symm p` lies in `M.integralPoints`. Both
  sides are rewritten with the published generic-coordinate descriptions
  `mem_baseChange_coefficientIntegralPoints_iff_genericCoordinates` and
  `mem_integralPoints_iff_genericCoordinates`.

For the two theorems below, `R` is in addition a noetherian domain. A
commutative group scheme `T` over `Spec K` and a homomorphism `iT : T.toGrp ⟶ G`
are given, with `IsSplitTorus T.toGrp` and `IsClosedSubgroup iT`. The
conclusion of both theorems is the same: there exist

* a commutative group scheme `𝒮` over `Spec R` with `IsSplitTorus 𝒮.toGrp`,
* a homomorphism `j : 𝒮.toGrp ⟶ M.group` with `IsClosedSubgroup j`, and
* an isomorphism `e` from the base change of `𝒮` along `Spec.algebraMap R K`
  to `T`,

such that `M.genericTorusMap 𝒮 j = CommGroupScheme.groupHom e.hom ≫ iT`. In
words, `iT` extends to a closed split torus of the model.

`exists_isSplitTorus_genericTorusMap_eq_of_baseChange`. Let `A` be a domain
that is a valuation ring, with fraction field `L` and infinite residue field.
Assume algebra maps `R → A`, `A → L`, `K → L` and `R → L` with scalar towers
`R → A → L` and `R → K → L`. Let `v` be a valuation on `L` with values in a
linearly ordered commutative group with zero. Assume:

* `hv`: `v` is one on the images of the units of `A`;
* `hint`: every `x : K` whose image in `L` lies in the image of `A` lies in the
  image of `R`;
* `hb`: the image of `characterValuationKernel v` of the base change of `T` to
  `L`, under the rational points of the base change of `iT`, is contained in
  `(M.baseChange A L).integralPoints`.

Then the conclusion above holds.

Proof. Write `T ≅ 𝔾_m^I` with `I` finite. Apply
`exists_isClosedSubgroup_genericTorusMap_eq` with `A` and `L`. Its unit-point
hypothesis is checked as follows. For `t : I → Aˣ`, the `L`-point of `𝔾_m^I`
with coordinates the images of `t` lies in the character valuation kernel by
`hv` and `baseChangeCoeffEquiv_symm_mem_characterValuationKernel`. Its image in
`T` lies in the kernel as well (`map_characterValuationKernel_le`). So by `hb`
its image in `G` is an integral point of `M.baseChange A L`. That is the
coefficient-integrality required, by `mem_coefficientIntegralPoints_iff`,
`baseChangeCoeffEquiv_map` and `affinePointsTarget_apply`. The resulting
`j : (torus R I).toGrp ⟶ M.group` is a closed subgroup. Its generic map is
`(genericSplitIso R K I).hom ≫ e.inv ≫ iT`. So `𝒮 = torus R I` with the
isomorphism `commIsoOfGroupIso (genericSplitIso R K I ≪≫ e.symm)` satisfies
the conclusion.

`exists_isSplitTorus_genericTorusMap_eq_of_bounded`. Assume moreover that `R`
is a valuation ring with infinite residue field. Let `v` be a valuation on `K`
with values in a linearly ordered commutative group with zero. Assume:

* `hv`: `v` is one on the images of the units of `R`;
* `hb`: the image of `characterValuationKernel v T.toGrp` under
  `rationalPoints.map iT` is contained in `M.integralPoints`.

Then the conclusion above holds. The proof is the same with `A = R` and
`L = K`. It uses `rationalCoeffEquiv_symm_mem_characterValuationKernel`,
`mem_baseChange_self_coefficientIntegralPoints_iff` and
`rationalCoeffEquiv_map`. The hypothesis `hint` holds trivially.

## Provenance

This module serves Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach*
(2023), Lemma B.2.3 and Proposition B.2.4 (printed pp. 655–656), for split
tori. In the book the hypothesis is that the maximal bounded subgroup of the
split torus lies in the integral points of the model. For a split torus with a
valuation that is one exactly on the units of the valuation ring, that subgroup
is the character valuation kernel used here (compare Kaletha–Prasad §2.6 and
§B.2). The theorems here assume only the one direction, that `v` is one on the
units.

The coordinate lemmas and `commIsoOfGroupIso` are internal bookkeeping with no
counterpart in the literature. Every ingredient other than the declarations of
`SplitTorusClosure` and `SplitTorusUnitPoints` is a published Library or
Mathlib result.

Drafted by Worker 5707 for Task 5707 (`f502c3c7-c095-4c74-bf82-ad8ffb916f57`, shared draft revision 2). The source is registered as `kaletha-prasad-2023-bruhat-tits-new-approach`.
