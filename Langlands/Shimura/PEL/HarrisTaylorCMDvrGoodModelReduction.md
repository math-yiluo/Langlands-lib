# Valuative extension of normalized Harris classes from good models

All declarations are in `Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel`. They carry
the variables and named prerequisites of the class presheaf
`smallLevelClassPresheafTower` (written "…" below).

## The good-model statement

`CMLevelDvrGoodModelStatement … U` is a proposition about a small level `U`. Let `V`
be a discrete valuation ring in `Type` with fraction field `K`, let
`β : Spec V ⟶ Spec F` be any structure morphism and let `a` be a geometric point of
the connected admissible test `connectedSpecTest … K (Spec.algebraMap V K ≫ β)`. Let
`x` be a representative of a normalized class at `U` over `Spec K` at `a`: an element
of `HarrisLevelData … a.hom … U.obj` whose positive polarized action satisfies the
normalized determinant condition and the numerical condition for
`Spec.algebraMap V K ≫ β`. The statement asks for an abelian scheme `G` over
`Spec V` and an isomorphism of abelian schemes from the generic fibre
`(baseChange (Spec.algebraMap V K)).obj G` to the abelian scheme of `x`. In words,
the abelian variety of every normalized representative over `K` at level `U` has good
reduction over `V`.

The module states this proposition and does not prove it. In the division case it
is expected from potential good reduction, the smallness of `U` and the criterion of
Néron, Ogg and Shafarevich.

## The reduction

`cmLevelDiscreteValuativeExistence_of_goodModels U hgood` proves the published
`CMLevelDiscreteValuativeExistenceStatement … U` (module
`HarrisTaylorCMDivisionCriteria`) from `CMLevelDvrGoodModelStatement … U`.

Fix `V`, `K` and `β`, and a geometric point `a` of `Spec K`. The published
`specTest_map_surjective_iff_pointed` reduces surjectivity of the presheaf
restriction along `specTestMap (algebraMap V K) β` to surjectivity of the pointed
restriction `geometricFamilyPointPullback` at `a`. By `classTowerBaseChangeAlong_eq`
this pointed restriction is the class pullback `classBaseChange` followed by a
transport along an equality of structure morphisms, which is bijective. The pointed
class pullback is surjective by `classBaseChange_surjective_of_levelMultipleLifts`:
the pointed monodromy map is surjective by `dvrGenericMonodromy_surjective`, and every
lower representative has a lift up to the multiplier `1/2`, obtained by applying
`dvrNormalizedLift_of_goodModel` to the good model that the hypothesis provides.

## Provenance

Internal. The module combines the published pointed reduction of
`HarrisTaylorCMDvrPointedReduction`, the DVR monodromy surjectivity of
`HarrisTaylorCMDvrMonodromy`, the aligned class pullback and the two companion
modules `HarrisTaylorCMMultipleClassReduction` and `HarrisTaylorCMDvrGoodModelLift`.
