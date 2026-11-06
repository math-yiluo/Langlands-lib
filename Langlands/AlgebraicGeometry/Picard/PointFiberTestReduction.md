# Point-fibre properties from finite-type affine tests

This module reduces properties of the schemes that represent actual Picard
point fibres to finite-type affine tests. It covers smoothness and
surjectivity, the two properties in the published
`PicardGroupoid.IsSmoothSurjectivePresentation`.

The setting is `f : X ⟶ S` and an actual line bundle `L` on
`(relativeSpace f).obj U` for `U : Over S`. Take a test `T : Over S` and an
actual line bundle `M` on `(relativeSpace f).obj T`. The published presheaf
`pointFiberPresheaf f L M` on `Over T.left` is the actual point fibre. Its
points over `Z` are maps to `U` together with actual isomorphisms of pulled-back
bundles.

Namespace: `Langlands.AlgebraicGeometry.Picard.PicardGroupoid`.

## Representing objects

- `uliftYonedaAdjunctionIso adj P :
  uliftYoneda.obj (G.obj P) ≅ F.op ⋙ uliftYoneda.obj P`, for an adjunction
  `adj : F ⊣ G` between categories with the same morphism universe. It is
  built from `adj.homEquiv` and naturality
  (`Adjunction.homEquiv_naturality_left_symm`).
- `schemeYonedaPullbackIso h P` is the case `Over.map h ⊣ Over.pullback h`
  for a morphism of schemes `h : T' ⟶ T` and `P : Over T`:
  `schemeYoneda T' (Over.pullback h P) ≅ (Over.map h).op ⋙ schemeYoneda T P`.
- `nonempty_iso_of_schemeYoneda`: two schemes over `T` whose scheme Yoneda
  presheaves are isomorphic to the same presheaf are isomorphic over `T`. The
  proof uses full faithfulness of `uliftYoneda`.
- `prop_hom_of_iso Q i`: a morphism property `Q` respecting isomorphisms
  passes from `P.hom` to `P'.hom` along `i : P ≅ P'` in `Over T`.

## Changing the test

- `iteratedSliceMapIso g : T'.iteratedSliceBackward ⋙ Over.map g ≅
  Over.map g.left ⋙ T.iteratedSliceBackward` for `g : T' ⟶ T` in `Over S`.
  Its components are identities on the underlying schemes.
- `testPullback f g M` is the actual line bundle
  `((relative f).map g.op.toLoc).toFunctor.obj (Core.mk M)`, the ordinary
  pullback of `M` along `(relativeSpace f).map g`. It is the bundle that the
  published relative pseudofunctor assigns.
- `pointFiberPresheafIsoOfIso f L e : pointFiberPresheaf f L M ≅
  pointFiberPresheaf f L M'` for an actual isomorphism
  `e : Core.mk M ≅ Core.mk M'`. It whiskers `isoPresheafIso` from
  `PseudofunctorPointFiberTestChange`.
- `pointFiberPresheafBaseChangeIso f L g M : pointFiberPresheaf f L
  (testPullback f g M) ≅ (Over.map g.left).op ⋙ pointFiberPresheaf f L M`. It
  whiskers `basePresheafIso` and composes with the opposite of
  `iteratedSliceMapIso g`.
- `pullbackRepresentationIso f L g e`: if `e` says that `P` represents the
  point fibre of `M`, then `Over.pullback g.left P` represents the point fibre
  of `testPullback f g M`.

## The point-fibre property

For a morphism property `Q` of schemes,
`PointFiberProperty f L Q T M : Prop` says that every `P : Over T.left` with
`Nonempty (schemeYoneda T.left P ≅ pointFiberPresheaf f L M)` has `Q P.hom`.

- `PointFiberProperty.of_exists`: if `Q` respects isomorphisms, one
  representing scheme with `Q` is enough, because representing schemes are
  unique up to isomorphism.
- `PointFiberProperty.of_iso`: the property passes along an actual
  isomorphism `Core.mk M ≅ Core.mk M'`.
- `PointFiberProperty.baseChange`: if `Q` is stable under base change, `P`
  represents `M`, and the property holds for `M`, then it holds for
  `testPullback f g M`. The pullback `pullback.snd P.hom g.left` is a
  representing scheme with `Q`.

## Finite-type affine tests

Now `S = Spec R` for a commutative ring `R : Type u`. The published
`affineBase R A` is the test `Spec A` over `Spec R`.
`FiniteTypeAffinePointFiberProperty f L Q : Prop` says the following. For every
`R`-algebra `B : Type u` of finite type and every actual line bundle `M` on
`(relativeSpace f).obj (affineBase R B)`, some representing scheme of the point
fibre has `Q`.

- `PointFiberProperty.affineBase`: assume `f` is quasi-compact and
  quasi-separated, `Q` is stable under base change, and the finite-type
  hypothesis holds. Then the property holds for every `R`-algebra `A` and every
  `M` over `affineBase R A`. The published
  `exists_affineFamily_subalgebra f M ∅` gives a finitely generated subalgebra
  `B ⊆ A`, a bundle `M₀` over `affineBase R B`, and an actual isomorphism from
  the pullback of `M₀` along `affineSubalgebraMap B` to `M`.
  `Subalgebra.fg_iff_finiteType` makes `B` of finite type. The finite-type
  hypothesis for `M₀`, then `of_exists`, `baseChange` and `of_iso`, give the
  claim.
- `coverAlgebra T i` makes the ring of the `i`-th member of
  `T.left.affineOpenCover` an `R`-algebra through `Spec.preimage` of the
  composite to `Spec R`. `coverMap T i` is the inclusion of that member as a
  map of tests `affineBase R _ ⟶ T`.
- `PointFiberProperty.of_finiteTypeAffine`: if, in addition, `Q` is
  Zariski-local on the target, the property holds for every test `T` and every
  `M`. For a representing `P`, `IsZariskiLocalAtTarget.of_openCover` with the
  affine open cover reduces `Q P.hom` to the pullbacks
  `pullback.snd P.hom (coverMap T i).left`. Each pullback represents the point
  fibre of `testPullback f (coverMap T i) M` (`pullbackRepresentationIso`), so
  `PointFiberProperty.affineBase` applies.

## Smooth surjective presentations

`isSmoothSurjectivePresentation_of_finiteTypeAffine f L` assumes `f` proper,
flat and locally of finite presentation. Its hypothesis is: for every
finite-type `R`-algebra `B` and every `M` over `affineBase R B`, both
`PointFiberProperty f L @Smooth (affineBase R B) M` and
`PointFiberProperty f L @Surjective (affineBase R B) M` hold. The conclusion is
`IsSmoothSurjectivePresentation f L`.

The published `hasAffinePointFiberSchemes f` supplies representing schemes for
all tests. The hypothesis then gives the finite-type affine hypothesis for
`@Smooth` and for `@Surjective`, and `of_finiteTypeAffine` gives both
properties for the representing scheme of every test. Mathlib's instances make
`Smooth` and `Surjective` stable under base change and Zariski-local on the
target.

## Provenance

This is internal infrastructure for the finite-type Picard stack atlas task.
It records the standard limit-and-locality reduction: properties of a
representing scheme that are stable under base change and local on the target
can be checked over affine tests of finite type over the base ring. The
limit step is the published `exists_affineFamily_subalgebra`. No cited source
theorem is formalized.

`prop_hom_of_iso` reuses `AlgebraicGeometry.prop_hom_of_overIso` on the
inverse isomorphism. The shared proof is the existing abelian-scheme helper
from `AbelianSchemeStructureOfOpenCoverProof`, with unchanged hypotheses.
