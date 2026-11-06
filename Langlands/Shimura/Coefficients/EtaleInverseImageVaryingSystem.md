# Inverse image of varying-torsor coefficient systems along arbitrary morphisms

This internal construction specializes the published comparison
`inverseImageAssociatedIso` to constant module coefficients, and assembles the
whole varying-torsor coefficient system. For an arbitrary morphism of schemes
and finite geometric torsors, the inverse image of the associated coefficient
system is naturally isomorphic to the associated system of the base-changed
torsors. The group diagram and the coefficient diagrams are unchanged. The
construction is the arbitrary-morphism analogue of the existing étale
comparison `etaleAssociatedVaryingSystemPullback`. All declarations are in
namespace `Langlands.Shimura.Coefficients`.

## Parameters and inputs

Let `X Z : Scheme.{u}`, let `f : Z ⟶ X` be any morphism, and let
`R : Type u` be a commutative ring. Groups and module carriers are in universe
`u`; the index category `I` has independent universes `uI`, `vI`. Write `f^*`
for the existing `inverseImage f R`. The inputs are the following existing
results:

- `inverseImageAssociatedIso`, `inverseImageProductSheafIso` and
  `inverseImageProductSheafMap_coverPullback` from
  `EtaleInverseImageAssociatedIso` and `EtaleInverseImageAssociated`;
- `inverseImageConstantIso` and `inverseImageConstantActionIso` from
  `Langlands.Geometry.EtaleInverseImageConstant`;
- the existing associated-sheaf functor `etaleAssociatedFunctor X Y`, which is
  the constant-sheaf action functor followed by `associatedFunctor`;
- the cross-cover maps `crossCoverMap` and `etaleCrossCoverMap`;
- the varying-cover constructions `etaleAssociatedAt`,
  `etaleAssociatedTransitionTarget`, `etaleAssociatedReduction`,
  `etaleAssociatedComparison`, `etaleAssociatedTransition` and
  `etaleAssociatedVaryingSystemFunctor`;
- geometric base change of covers and cover diagrams,
  `etaleTorsorPullbackFunctor` and `etaleTorsorDiagramPullback`.

## Constant coefficients

Let `G : Type u` be a group and `Y : Action X.Etale G`; write `Y_f` for
`(etaleTorsorPullbackFunctor f G).obj Y`.

- `inverseImageConstantAssociatedMap f R Y` is the natural transformation
  `etaleAssociatedFunctor X Y ⋙ f^* ⟶ etaleAssociatedFunctor Z Y_f`. It is the
  associated-sheaf comparison at constant coefficient actions, followed by
  `associatedFunctor` applied to `inverseImageConstantActionIso`.
- `inverseImageConstantAssociatedMap_inclusion` states that the map followed
  by the invariant inclusion for `Y_f` equals inverse image of the original
  inclusion, followed by the product-sheaf base-change map, followed by the
  product sheaf of `inverseImageConstantIso` at the underlying module.
- For `hY : IsFiniteGeometricTorsor X Y`,
  `inverseImageConstantAssociatedIso f R Y hY` is the natural isomorphism with
  this forward map (`inverseImageConstantAssociatedIso_hom`). It whiskers
  `inverseImageAssociatedIso` and `inverseImageConstantActionIso`.
  `inverseImageConstantAssociatedIso_hom_inclusion` restates the inclusion
  formula with `inverseImageProductSheafIso`.
  `inverseImageConstantAssociatedIso_inv_inclusion` states that the inverse map
  followed by inverse image of the original inclusion is the inclusion for
  `Y_f`, followed by the product sheaf of the inverse constant-sheaf
  comparison and the inverse of `inverseImageProductSheafIso`.
- `inverseImageConstantAssociatedMap_crossCover` states compatibility with
  every cross-cover map. For a group homomorphism `φ : H →* G`, a cover map
  `a : Y' ⟶ (Action.res X.Etale φ).obj Y` and a coefficient map
  `c : (Action.res _ φ).obj M ⟶ N`: inverse image of `etaleCrossCoverMap X φ a c`
  followed by the comparison for `Y'` equals the comparison for `Y` followed
  by `etaleCrossCoverMap Z φ ((etaleTorsorPullbackFunctor f H).map a) c`. The
  coefficient map is unchanged. The proof compares invariant inclusions. It
  uses naturality of the product-sheaf base-change map and its compatibility
  with `coverPullback`, both existing, together with `coverPullback_natural`
  and naturality of `inverseImageConstantIso`.

## Varying-torsor systems

Let `D : I ⥤ GrpCat.{u}`, `Y : EquivariantDiagram D X.Etale` and
`hY : ∀ i, IsFiniteGeometricTorsor X (Y.action i)`. Write `Y_f` for
`(etaleTorsorDiagramPullback f D).obj Y`. Its finite-torsor hypothesis is
the existing `etaleTorsorDiagramPullback_isFiniteGeometricTorsor f D Y hY`.

- `inverseImageAssociatedAtIso f R Y hY i` is the natural isomorphism
  `etaleAssociatedAt X Y i ⋙ f^* ≅ etaleAssociatedAt Z Y_f i`. It is
  `inverseImageConstantAssociatedIso` at index `i`, natural in the entire
  coefficient diagram.
  `inverseImageAssociatedTransitionTargetIso f R Y hY b` is the same comparison
  for the common target of reduction and cover change.
- `etaleAssociatedReduction_inverseImage` is naturality of the comparison in
  the coefficient transition. `etaleAssociatedComparison_inverseImage` is the
  cross-cover compatibility for the cover transition `Y.transition b` with the
  identity coefficient map.
- `etaleAssociatedTransition_inverseImage` states that inverse image of the
  existing inverse-cover transition, followed by the comparison at `j`, equals
  the comparison at `i` followed by the transition for `Y_f`. The proof
  cancels the invertible cover comparison of `Y_f`, which is the existing
  `etaleAssociatedComparison_app_isIso`. The two previous squares and the
  existing `etaleAssociatedTransition_comparison` complete it, as in the étale
  case.
- `etaleAssociatedVaryingSystemInverseImage f R Y hY` is the natural
  isomorphism

  ```text
  etaleAssociatedVaryingSystemFunctor X Y hY ⋙ (whiskeringRight I _ _).obj f^*
    ≅ etaleAssociatedVaryingSystemFunctor Z Y_f _
  ```

  of functors on coefficient diagrams. `_hom_app` and `_inv_app` identify its
  components with `inverseImageConstantAssociatedIso` and its inverse at each
  index. `etaleAssociatedTransition_inverseImage_inv` is the transition square
  for the inverse comparison.

## Scope and provenance

The coefficient reductions and the group diagram are those of the original
system; nothing is reindexed or replaced. The module makes no cohomological,
derived, lisse-adic or Shimura-variety assertion. It does not construct the
CM-specific identification with `cmHarrisGeometricCoefficientSystem`, which
belongs to the consumer modules.

This is internal infrastructure assembled from the published comparisons
listed above and Mathlib's whiskering and natural-isomorphism constructions.
No external-literature statement is formalized.
