# Lifting along the dual numbers for the effective Picard tower bundle

This internal module proves condition (1) of Stacks Lemma 90.13.2, in its
actual-point form, for the published effective line bundle of the Picard source
tower. Points lift along the dual-number augmentation, given the same property
for the initial stage family. All declarations are in the namespace
`Langlands.AlgebraicGeometry.Picard.PicardGroupoid.ArtinianPicardTowerTangentLifting`.

## A point factoring through a restricted atlas object

`exists_mapPoints_eq`: let `F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat` be a pseudofunctor,
`i : V ⟶ U` an arrow of `C`, `ξ` an object over `U` and `η` an object over `S`.
Let `x` be a published point (`PseudofunctorPointFiber.Points F ξ η Z`) whose
map to `U` factors as `a ≫ i`. Then `x` is the image, under the published
`PseudofunctorPointFiberAtlasRestriction.mapPoints`, of a point of the
restricted object `i^* ξ` with map `a`. This is the single-point case of the
published `mapPoints_surjective`, with the same proof.

## Transfer of lifting along the dual numbers

`hasLiftingForAt_dualReduction_of_pullback`. Let `k` be a commutative ring,
`K` a field with a `k`-algebra structure, and `f : X ⟶ Spec k`. Let `H` be a
`k`-algebra, `L` an actual line bundle on the base change of `X` to `Spec H`,
and `p` a residue point of `Spec H`. Let `T₀` be a test, `L₀` an actual line
bundle on the base change to `T₀`, and `i : base T₀ ⟶ Spec H` a map over
`Spec k` with `reduction T₀ ≫ i = p`. Suppose an isomorphism of line bundles
`i^* L ≅ L₀` is given, and suppose the published
`HasLiftingForAt f L₀ (reduction T₀) (dualReduction k K)` holds. Then
`HasLiftingForAt f L p (dualReduction k K)` holds.

Proof: let `y` be a point of `L` over a residue map, with closed point `p`. By
the published `reduction_residue`, `y.1 = p = reduction T₀ ≫ i`. By
`exists_mapPoints_eq`, `y` comes from a point of `i^* L`. The isomorphism
`i^* L ≅ L₀` (published `PseudofunctorPointFiberObjectIso.mapPoints`) turns it
into a point `z` of `L₀` at the closed point of `T₀`. Lift `z` along the dual
numbers by the hypothesis. Then map the lift back through the inverse
isomorphism and `mapPoints`. The published naturality lemmas
`mapPoints_restrict` (for both point maps) and
`PseudofunctorPointFiberObjectIso.mapPoints_symm` show that the result
restricts to `y`.

## The effective bundle

Let `R` be a complete Noetherian local `k`-algebra with surjective
augmentation `ε : R → K`. Let `f` be flat and proper, and let `s₀` be a
published `ArtinianPicardSourceStep.Stage ε f M`. Write `H`, `L` and `p` for
the published limit ring, effective bundle and closed point.

- `nonempty_initialIso`: the pullback of `L` along the spectrum of the published
  projection `projection 0 : H → test 0` is isomorphic to the published stage-0
  bundle `ArtinianPicardTowerFamily.bundle 0`. The published
  `effectiveEvaluationIso` (with a bound from `exists_bound`) identifies it with
  the pullback of the stage bundle at `index a` along `stageMap`. By the
  published `towerMap_unique`, `stageMap` is the tower map. The published
  `hasTransition` identifies that pullback with the stage-0 bundle.
- `hasLiftingForAt_dualReduction`: if
  `HasLiftingForAt f s₀.family.right.of (reduction s₀.test) (dualReduction k K)`,
  then `HasLiftingForAt f L p (dualReduction k K)`. This applies
  `hasLiftingForAt_dualReduction_of_pullback` with `i` the spectrum of
  `projection 0`. The equation `reduction (test 0) ≫ i = p` is the published
  `augmentation_projection`.

## Provenance

Internal. In Stacks Project Lemma 90.13.4 (Tag 06IW, Chapter 90 Formal
Deformation Theory), condition (1) of Lemma 90.13.2 (surjectivity on tangent
spaces) for the hull comes from the choice of the second stage ξ₂. Here the
same role is played by the initial stage, and the condition is lifting of
actual points along the dual numbers rather than surjectivity of a linear map.
