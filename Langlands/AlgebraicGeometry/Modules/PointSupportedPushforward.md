# Recognizing modules supported at one closed point from their sections over an affine open

This module shows that a module `N` on a scheme `Y`, supported at a closed
point `i pt` given by a section `i : Spec k ⟶ Y` of a morphism
`s : Y ⟶ Spec k` (`k` a field), is the pushforward `i_* 𝒪_{Spec k}` as soon
as its sections over one affine open `V ∋ i pt` form the residue ring of
`Γ(Y, V)` at `i pt`; and that it is zero as soon as these sections vanish.
All declarations live in the namespace
`Langlands.AlgebraicGeometry.Modules.DerivedSections`, and `affineSections`
is the one from `AffineHigherDirectImageSections`.

## Statements

### Germs of affine sections

Let `V` be an affine open of `Y` (`hV : IsAffineOpen V`) and `N : Y.Modules`.
The affine sections are, as an abelian group, the sections of `N` over the
open `V.ι ''ᵁ (hV.isoSpec.hom ⁻¹ᵁ ⊤)` of `Y` (which is `V`).

- `mem_image_preimage_top hV hy`: a point `y ∈ V` lies in that open.
- `affineSectionsGerm hV N hy`: the additive germ map
  `affineSections hV N →+ stalk N y` at `y ∈ V`.
- `affineSectionsGerm_smul hV N hy r m`: for `r : Γ(Y, V)`, the germ of
  `r • m` is `Y.presheaf.germ V y hy r • (germ of m)`.
- `isZero_of_isZero_affineSections hV hy hcl N hN h`: if `y ∈ V`, `{y}` is
  closed, `stalkSupport N ⊆ {y}` and `affineSections hV N` is zero, then
  `N` is zero.

### A linearity criterion over localizations

- `linearEquivOfIsLocalization S f hf`: let `A` be a localization of the
  commutative ring `R` at the submonoid `S`, and `M`, `N` two `A`-modules.
  An additive equivalence `f : M ≃+ N` with
  `f (algebraMap R A r • m) = algebraMap R A r • f m` for all `r`, `m` is an
  `A`-linear equivalence `M ≃ₗ[A] N` with the same underlying map.

### Evaluation at a rational point

Let `k` be a field, `pt` the point of `Spec (CommRingCat.of k)`,
`i : Spec (CommRingCat.of k) ⟶ Y`, and `V` an open with `hy : i pt ∈ V`.

- `germ_top_surjective_of_field pt`: the germ map from global functions of
  `Spec k` to its stalk at `pt` is surjective.
- `eq_zero_of_not_isUnit_stalk_of_field pt z hz`: a nonunit `z` of that
  stalk is zero.
- `pointEval pt i hy`: the ring homomorphism
  `Γ(Y, V) →+* (Spec k).presheaf.stalk pt`, the germ at `i pt` followed by
  the stalk map `i.stalkMap pt`; `pointEval_apply` unfolds it.
- `pointEval_eq_zero_iff pt i hy hV r`: for affine `V`, `pointEval pt i hy r`
  is zero iff `r` lies in the prime ideal `hV.primeIdealOf ⟨i pt, hy⟩`.
- `pointEval_surjective pt i hy s his`: if `s : Y ⟶ Spec k` satisfies
  `his : i ≫ s = 𝟙 _`, then `pointEval pt i hy` is surjective.

### Recognition of the pushforward

Now additionally `s : Y ⟶ Spec (CommRingCat.of k)` with `his : i ≫ s = 𝟙 _`
and `hV : IsAffineOpen V`. Write `𝔭 := (hV.primeIdealOf ⟨i pt, hy⟩).asIdeal`.

- `quotientPointEquiv pt i s his hV hy`: the ring isomorphism
  `Γ(Y, V) ⧸ 𝔭 ≃+* (Spec k).presheaf.stalk pt`;
  `quotientPointEquiv_mk` says it sends the class of `r` to
  `pointEval pt i hy r`.
- `nonempty_stalk_iso_of_affineSections_iso pt i s his hV hy N hcl hN e`:
  if `{i pt}` is closed, `stalkSupport N ⊆ {i pt}`, and
  `e : affineSections hV N ≅ ModuleCat.of Γ(Y, V) (Γ(Y, V) ⧸ 𝔭)`, then the
  stalk `(stalkFunctor (i pt)).obj N` is isomorphic, as a module over
  `Y.presheaf.stalk (i pt)`, to the stalk at `pt` of the unit module of
  `Spec k` with scalars restricted along `i.stalkMap pt`.
- `nonempty_iso_pushforward_of_affineSections_iso pt i s his hV hy N hcl hN e`:
  under the same hypotheses,
  `N ≅ (Scheme.Modules.pushforward i).obj
  (Langlands.Scheme.Modules.structureSheaf (Spec (CommRingCat.of k)))`.

## Implemented proof

`affineSectionsGerm_smul`: the scalar action of `r` on the affine sections
is, by definition, the action of the corresponding function `a0` on
`V ≅ Spec Γ(Y, V)` on sections of the restriction; the published
`Scheme.Modules.smul_restrictAppIso_hom_apply` turns this into the action of
`(V.ι.appIso _).inv a0` on sections of `N`. `PresheafOfModules.germ_smul`
moves the germ inside, and the remaining identity of germs of functions
follows from `IsAffineOpen.isoSpec_hom_appTop`, `Scheme.Opens.ι_appIso`,
`Scheme.Opens.topIso_inv` and `germ_res_apply`.

`isZero_of_isZero_affineSections`: by `stalkSupport_eq_empty_iff` it
suffices that no point lies in the stalk support. Such a point equals `y`,
and the germ map from the affine sections to the stalk at `y` is bijective
(`germ_bijective_of_stalkSupport_subset` from `PointSupportedSkyscraper`);
since the affine sections form a subsingleton, so does the stalk,
contradicting `mem_stalkSupport_iff_nontrivial`.

`linearEquivOfIsLocalization`: give `M` and `N` the `R`-module structures
through `algebraMap R A`, so that they become scalar towers; `hf` makes `f`
`R`-linear, and Mathlib's `LinearEquiv.extendScalarsOfIsLocalization`
extends it to an `A`-linear equivalence.

`germ_top_surjective_of_field`: every open of `Spec k` containing `pt` is
`⊤`, since `Spec k` has one point; restrict a representing section to `⊤`.
`eq_zero_of_not_isUnit_stalk_of_field`: write `z` as the germ of a global
function `a`; if `a ≠ 0` then its image in the field `k` under
`Scheme.ΓSpecIso` is a unit, hence `a` and its germ are units.

`pointEval_eq_zero_iff`: the stalk at `i pt` is the localization of
`Γ(Y, V)` at `𝔭` (`IsAffineOpen.isLocalization_stalk`), so the germ of `r`
is a unit iff `r ∉ 𝔭` (`IsLocalization.AtPrime.isUnit_to_map_iff`). Since
`i.stalkMap pt` is a local homomorphism, the germ of `r` is a unit iff its
image `pointEval pt i hy r` is a unit, and in the stalk of `Spec k` the
nonunits are exactly zero by the previous lemma (and zero is not a unit).

`pointEval_surjective`: every element is the germ of a global function `c`
of `Spec k`; the restriction to `V` of `s.appTop c` maps to it, because
the germ at `pt` of `(i ≫ s).appTop c` is the germ of `c` (as
`i ≫ s = 𝟙`) and `Hom.germ_stalkMap_apply` computes the stalk map on germs.

`quotientPointEquiv` composes `Ideal.quotEquivOfEq` (the kernel of
`pointEval` is `𝔭`) with `RingHom.quotientKerEquivOfSurjective`.

`nonempty_stalk_iso_of_affineSections_iso`: let `G` be the germ map from
the affine sections to the stalk at `i pt`, an additive equivalence by
`germ_bijective_of_stalkSupport_subset`. The additive equivalence
`G⁻¹`, then `e`, then `quotientPointEquiv`, then the inverse of the
published `unitStalkLinearEquiv` (the stalk of the unit module is the local
ring) commutes with the action of `Γ(Y, V)`: on `G m` the action of `r` is
`G (r • m)` by `affineSectionsGerm_smul`, `e` is `Γ(Y, V)`-linear, and
`quotientPointEquiv` and `pointEval` are multiplicative. Since the stalk at
`i pt` is the localization at `𝔭`, `linearEquivOfIsLocalization` upgrades it
to a linear equivalence over the stalk.

`nonempty_iso_pushforward_of_affineSections_iso`: compose
1. `isoSkyscraperOfStalkSupportSubset` for `N` at the closed point `i pt`;
2. the skyscraper functor at `i pt` applied to the stalk isomorphism above;
3. the inverse of the published `StalkPullback.skyscraperPushforwardIso i pt`,
   which identifies the skyscraper at `i pt` of a restricted-scalars module
   with the pushforward along `i` of the skyscraper at `pt`;
4. the pushforward along `i` of the inverse of
   `isoSkyscraperOfStalkSupportSubset` for the unit module on `Spec k`,
   whose support is trivially contained in the closed set `{pt} = univ`.

The structure sheaf `Langlands.Scheme.Modules.structureSheaf` is the unit
module `SheafOfModules.unit`, so the last step lands in the stated target.

## Provenance and scope

These are internal helpers for the direct-image half of Edixhoven, van
der Geer and Moonen, *Abelian Varieties* (registered source
`edixhoven-vandergeer-moonen-abelian-varieties-draft`), Theorem (9.1): there the top direct image
`R^g p_* P` is computed, through its sections over an affine neighbourhood
of the origin of the dual, to be the residue field at the origin, and the
lower ones to vanish. The route through stalks (skyscraper recognition and
a localization linearity argument) replaces the direct computation of the
affine sections of `i_* 𝒪_{Spec k}`; it is not taken from the literature.
