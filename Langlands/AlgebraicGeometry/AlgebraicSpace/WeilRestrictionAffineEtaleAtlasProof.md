# Proof of the affine-atlas input for restriction of scalars of algebraic spaces

Author: Worker 185.

`Langlands.AlgebraicGeometry.AlgebraicSpace.weilRestrictionAffineEtaleAtlas`
proves the Library statement `WeilRestrictionAffineEtaleAtlasStatement` from
`WeilRestrictionGeometricInputsStatement`. This is the affine-atlas input for
Conrad, *Weil and Grothendieck approaches to adelic points*
(December 31, 2011), Lemma 5.10, printed pp.17–18 (registered source
`conrad-2011-weil-grothendieck-adelic-points`). Let `R'` be a finite projective
`R`-algebra and `X'` a quasi-separated algebraic space over `Spec R'`. Let
`a : U' → X'` be étale and surjective, with `U'` an affine scheme locally of
finite type over `Spec R'`. Then the restricted transformation
`Functor.whiskerLeft (Over.pullback (Spec.algebraMap R R')).op a` is étale and
surjective. These are properties of the transformation of full restricted
presheaves on schemes over `Spec R`, as in the statement; representability of
the restricted space is not assumed.

The theorem combines two results:

- `WeilRestrictionAtlas.weilRestrictionAffineEtaleAtlas_of_representationInput`
  (module `WeilRestrictionAtlasReduction`) derives the statement from the
  internal proposition `WeilRestrictionAtlas.RepresentationInput`. It
  base-changes the restricted atlas along a test point over a scheme `V`. This
  reduces the claim to representing, over `V`, the restriction of an étale
  surjective quasi-compact separated scheme `Y` over `V ×_{Spec R} Spec R'` by
  an étale surjective scheme. Quasi-compactness and separation of `Y` come from
  quasi-separatedness of `X'` and affineness of `U'`.
- `WeilRestrictionAtlas.representationInput` (module
  `WeilRestrictionAtlasLocalRepresentation`) proves `RepresentationInput`. Over
  each affine chart `Spec A` of `V`, the base change of `Y` to
  `Spec (A ⊗[R] R')` is quasi-affine by Zariski's main theorem. Its glued
  affine-chart Weil restriction represents the restricted presheaf there and is
  étale (module `PointTopology.AffineChartWeilRestrictionEtale`) and surjective
  (module `PointTopology.AffineChartWeilRestrictionSurjective`). The charts glue
  to a representing scheme over `V`, which is étale and surjective because
  both properties are local on the target.

The module `TestFibreRepresentation` supplies the generic step from a
representation of a fibre presheaf over `V.left` to a pullback square over the
base. The hypothesis `LocallyOfFiniteType U'.hom` of the statement is not used;
étaleness of `a` already makes the base change `Y` locally of finite type. The
proof does not use the space-level Weil restriction representability statement
`SpaceWeilRestrictionStatement` or the diagonal input
`WeilRestrictionDiagonalStatement`.
