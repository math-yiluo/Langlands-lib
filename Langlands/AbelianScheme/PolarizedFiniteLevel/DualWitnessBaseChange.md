# Transporting supplied dual witnesses under base change

Module `Langlands.AbelianScheme.PolarizedFiniteLevel.DualWitnessBaseChange`.
All declarations are in
`Langlands.AbelianScheme.PolarizedFiniteLevel` and work for schemes in an
arbitrary fixed universe `u`.

## Inputs and scope

Let `b : S' ⟶ S`, let `A : AbelianScheme S`, and supply
`hA : HasDualScheme A`. The named premise
`universality : PicardZeroUniversalBaseChangeStatement.{u}` gives
`hA' := hasDualScheme_baseChange universality b A hA` for
`A' := (AbelianScheme.baseChange b).obj A`.
Write `D := dualScheme A hA` and `D' := dualScheme A' hA'`.
The actual canonical comparison is

`e : (Over.pullback b).obj D ≅ D'`,

given by `dualSchemeBaseChangeIso universality b A hA hA'`.

This module transports the dual geometry and a supplied tensor inverse
and evaluation. It requires no restriction on the morphism `b` or either
base. In particular, local noetherianity and invertibility of a level
are not needed for these witness constructions.

## Geometry

`dualSchemeGeometry_baseChange universality b A hA geometryA hA'`
proves `DualSchemeGeometry A' hA'` from
`geometryA : DualSchemeGeometry A hA`. Here its final argument may be
any supplied proof of `HasDualScheme A'`, including the derived proof
above.

The implemented proof first applies stability under base change to the
smoothness, properness and geometric connectedness of `D.hom`.
It then uses the inverse of the canonical comparison to transport these
properties to the chosen dual of `A'`. Smoothness and properness follow
by composition with the underlying isomorphism. For geometric
connectedness the commutative square with that isomorphism on top and
`𝟙 S'` on the bottom is Cartesian; stability under base change applies
to this square. Thus no relative dual-geometry theorem is assumed.

## Tensor inverse and evaluation

The remaining definitions use the derived proof `hA'` above.
`dualWitnessBaseChangeSpaceMap universality b A hA` is the actual map

`q : D' ×[S'] A' ⟶ D ×[S] A`

defined by

`(relativeSpace A'.X.hom).map e.inv ≫ baseChangeFamilySpaceMap b A D`.

Let `P` and `P'` be the module sheaves underlying the original and
changed Poincare line bundles. The published
`poincareBaseChangeForgetPullbackIso` gives `P' ≅ q*P`.
For a supplied ordinary line bundle `MA` on `D ×[S] A`,
`dualWitnessBaseChangeInverseBundle universality b A hA MA`
is the ordinary line bundle `q*MA`.

`dualWitnessBaseChangeEvaluation universality b A hA MA preservation
evaluationA` takes the explicit premise
`preservation : pullbackTensorComparisonIsIsoStatement.{u}` and an
actual evaluation isomorphism

`evaluationA : P ⊗ MA.obj ≅ O`.

It constructs the actual evaluation

`P' ⊗ (q*MA).obj ≅ O`

on `D' ×[S'] A'`. Its implementation tensors the module isomorphism
`P' ≅ q*P` with the identity of the second factor, then composes with
`pullbackTensorEvaluation preservation q P MA.obj evaluationA`.
That published construction uses the inverse tensor pullback comparison,
the pullback of `evaluationA`, and the fixed pullback-unit isomorphism.

No existence of tensor inverses is asserted: an inverse bundle and an
evaluation on the original dual product are supplied. The changed
inverse and evaluation are constructed from them. Together with the
geometry result and `hasDualScheme_baseChange`, these definitions give
the raw witnesses needed to assemble a changed dual in the polarized
finite-level datum. This module does not define that bundled datum,
its isomorphisms, its quotient, or its restriction functor.

## Provenance

These are derived categorical constructions for transporting the
existing Library witnesses. Their inputs and conventions are those of
`DualSchemeBaseChange`, `PoincareSliceSymmetryBaseChange`,
`GeometricPicardZeroInverse` and
`RelativeDualSchemeGeometryStatement`. The geometric proof uses
Mathlib's stability of smooth, proper and geometrically connected
morphisms under base change and the Cartesian square of an
isomorphism. The evaluation construction composes the actual
Poincare comparison and tensor pullback isomorphisms already in the
Library. No additional literature theorem or universal dual-existence
premise is introduced.
