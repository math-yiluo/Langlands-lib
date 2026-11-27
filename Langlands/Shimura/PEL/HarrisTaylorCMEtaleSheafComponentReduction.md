# Étale descent of the normalized CM classes from connected admissible tests

The module `Langlands.Shimura.PEL.HarrisTaylorCMEtaleSheafComponentReduction`
proves

```lean
theorem cmSmallLevelEtaleSheafStatement_of_connected
    (hconn : CMConnectedEtaleSheafStatement D C …) :
    CMSmallLevelEtaleSheafStatement D C …
```

for the same universe-zero data and named prerequisites as both propositions.
So the étale sheaf condition of the normalized class presheaf
`(smallLevelClassPresheafTower …).obj U` on all componentwise admissible tests
follows from the same condition for the unpointed class presheaf on connected
admissible tests. The argument only reorganizes the cover by connected
components; it uses no property of abelian schemes.

## Notation

`DisBases` is `ComponentwiseAdmissibleCMBaseCategory D C …` and `Bases` is
`AdmissibleCMBaseCategory D C …`. For a test `X : DisBases` and a connected
component `c` of its underlying scheme, `componentCMBase … X c : Bases` is the
open component scheme with its restricted structure map. For a test morphism
`f : Y ⟶ X`, a component `d` of `Y` and a component `c` of `X` with
`componentMap f.hom.left d = c`, `componentCMBaseHomTo … f d c _` is the
restriction of `f` to these components. The value of the disconnected
presheaf at `X` is the product over the components `c` of the unpointed class
sets at `componentCMBase … X c`, and its restriction along `f` takes the
`d`-coordinate from the unpointed pullback along the component restriction
(`disconnectedClassTowerPullback_app_eq`).

## Auxiliary declarations

- `componentMap_comp_componentι`: a scheme morphism into the component scheme
  of `d`, followed by the component inclusion, sends every connected component
  of its source to `d`.
- `connectedCMTest Z`: a connected admissible test `Z` regarded as an object of
  `DisBases`. Its componentwise admissibility comes from the published
  `componentwiseAdmissibleCMBase_of_relativeDual` and the proved relative dual
  statements `relativeDualSchemeExistence` and `relativeDualSchemeGeometry`.
- `componentSourceHom X d Z a`: for `a : Z ⟶ componentCMBase … X d` in `Bases`,
  the test morphism `connectedCMTest Z ⟶ X` whose underlying scheme morphism is
  `a.hom.left ≫ componentι X.obj.left d`.
- `componentCMBaseHomTo_componentSourceHom`: the restriction of
  `componentSourceHom X d Z a` to a component `z` of `Z` and to `d` is the
  canonical isomorphism `componentCMBaseInclusionIso` from the component scheme
  of `z` to `Z`, followed by `a`. The proof compares both sides after the
  component inclusion of `d` (`componentHomTo_unique`).
- `unpointedClassTowerPullback_app_injective_of_iso`: pullback of unpointed
  classes along an isomorphism of connected tests is injective, since pullback
  along the inverse undoes it (`unpointedClassTowerPullback_comp`,
  `unpointedClassTowerPullback_id`).
- `disconnectedClassTowerPullback_componentSourceHom_apply`: the `z`-coordinate
  of the disconnected pullback of `v` along `componentSourceHom X d Z a` is the
  pullback of the unpointed class `v d` along `a`, followed by pullback along
  `componentCMBaseInclusionIso`.

## Proof of the reduction

Let `U` be a small level, `S` a test and `f i : T i ⟶ S` (`i : J`) étale test
morphisms whose images cover `S`. By Mathlib's `Presieve.isSheafFor_arrows_iff`
it suffices to show that every compatible family `x i` has exactly one
amalgamation.

Fix a component `c` of `S`. Its pieces are indexed by the type `K c` of pairs
`(i, d)` with `d` a component of `T i` and `componentMap (f i).hom.left d = c`.
The pieces are the connected tests `componentCMBase … (T i) d` with the
component restrictions `componentCMBaseHomTo … (f i) d c _` to
`componentCMBase … S c`. These are étale: they are restrictions `resLE` of
étale morphisms to open subschemes. They cover the component of `S`: a point
`p` of the component is the image of a point `y` of some `T i`, and `y` lies in
its own component `d`, which `f i` maps to `c`; the image of `y` in the
component scheme of `c` is `p` because the component inclusion is injective.

The coordinates `x i d` with `(i, d)` in `K c` are compatible on connected
tests. Let `Z` be a connected admissible test with morphisms `a` and `b` to the
pieces `(i, d)` and `(j, e)` whose composites to the component of `S` agree.
The two test morphisms `componentSourceHom … (T i) d Z a` and
`componentSourceHom … (T j) e Z b` then have equal composites with `f i` and
`f j`, because the component restrictions commute with the component
inclusions (`componentHomTo_ι`). Compatibility of the original family gives
equal pullbacks of `x i` and `x j` to `connectedCMTest Z`. Evaluated at a
component `z` of `Z`, which exists because a connected space is nonempty, the
auxiliary formula turns this into the equality of the pullbacks of `x i d`
along `a` and of `x j e` along `b`, followed by the same pullback along an
isomorphism. That last pullback is injective.

The hypothesis `CMConnectedEtaleSheafStatement`, applied to the component of
`c` with these pieces, gives a unique unpointed class `w c` on the component
whose pullback to each piece `(i, d)` is `x i d`. The family `t = (w c)_c` is an
element of the disconnected presheaf at `S`. Its pullback along `f i` has
`d`-coordinate the pullback of `w (componentMap (f i).hom.left d)` along the
component restriction, which is `x i d`; so `t` is an amalgamation. If `t'` is
another amalgamation, then for every `c` and every piece `(i, d)` over `c` the
`d`-coordinate of the pullback of `t'` along `f i` is the pullback of `t' c`,
so `t' c` satisfies the defining property of `w c`, and uniqueness gives
`t' c = w c`.

## Provenance

This is an internal derivation from the definitions of the disconnected and
connected class presheaves in
`Langlands.Shimura.PEL.HarrisTaylorCMPolarizedDisconnectedPresheaf` and
`Langlands.Shimura.PEL.HarrisTaylorCMPolarizedUnpointedPresheaf`, the component
schemes of `Langlands.AlgebraicGeometry.LocallyNoetherianComponentSchemes`,
the admissibility criterion of `Langlands.Shimura.PEL.HarrisTaylorCMBaseAdmissibility`
and Mathlib's description of the sheaf condition for a family of arrows.
