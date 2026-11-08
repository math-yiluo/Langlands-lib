# Reductions of actual Picard chart versality

Module `Langlands.AlgebraicGeometry.Picard.ArtinianChartTestReduction`, namespace
`Langlands.AlgebraicGeometry.Picard.PicardGroupoid.ArtinianChartTestReduction`.
Author: Worker 967 (task `14dfbe95-4d4a-46fd-933a-182df994126c`, openness of
versality for actual Picard families).

This module gives two reductions of the Library's pointed versality
`ArtinianChartVersality.IsFormallyVersalAt`. Both are later used to reduce
openness of versality to an affine chart and to a single test bundle on the
spectrum of the source test ring. Everything is proved in the file. There are no
hypotheses beyond those in the signatures.

## Setting

`R : Type u` is a commutative ring and `f : X ⟶ Spec R` a morphism of schemes.
`U : Over (Spec R)` carries an actual line bundle `L` on
`(relativeSpace f).obj U`. For a field `K` with an `R`-algebra structure,
`p : ArtinianTest.residueBase R K ⟶ U` is a specified residue point. For tests
`A B : ArtinianTest R K` and an arrow `q : A ⟶ B`, `FiberPoints f L N Z` are the
Library's actual point fibres. Each point consists of a map to `U` and an actual
isomorphism of pulled-back bundles. `restrict f L q N w` is the Library's
coherent restriction along `ArtinianTest.baseMap q`.

## Declarations

- `HasBaseLiftingForAt f L p q`: for every actual line bundle `N` on
  `(relativeSpace f).obj (ArtinianTest.base A)` and every point `y` of the fibre
  over `Over.mk (ArtinianTest.baseMap q)` whose residue map
  `ArtinianTest.reduction B ≫ y.1` is `p`, there is a point `x` over
  `Over.mk (𝟙 (ArtinianTest.base A))` with `restrict f L q N (Category.comp_id _) x = y`.
  This is the Library's `HasLiftingForAt f L p q` restricted to the test
  `T = ArtinianTest.base A` with `a = 𝟙`.

- `hasLiftingForAt_iff_base f L p q`:
  `HasLiftingForAt f L p q ↔ HasBaseLiftingForAt f L p q`.
  The forward direction specializes `T`, `a`, `b`. For the converse, let a slice
  test `T`, a bundle `M` on `(relativeSpace f).obj T`, `a : base A ⟶ T` and a point
  `y` over `Over.mk (baseMap q ≫ a)` be given. Pull `M` back along `a` with the
  Library's relative pseudofunctor to get `N`. The Library equivalence
  `PseudofunctorPointFiberTestChange.basePointsEquiv` turns `y` into a point over
  `Over.mk (baseMap q)` for `N`, with the same base map, hence the same residue
  map. Lift it with the hypothesis and transport the lift back with the same
  equivalence. Then restrict along the identity slice arrow
  `Over.mk a ⟶ Over.mk (𝟙 ≫ a)`. `PseudofunctorPointFiber.restrict_comp` and
  `basePointsEquiv_restrict` show that the result restricts to `y`. The two
  composite slice arrows agree because both have underlying map `baseMap q`.

- `isFormallyVersalAt_of_restrictBundle f L ι p h`: let `ι : V ⟶ U` be an arrow
  of `Over (Spec R)` whose underlying map is an open immersion. Let
  `p : residueBase R K ⟶ V`. If the Library's `restrictBundle f L ι` is formally
  versal at `p`, then `L` is formally versal at `p ≫ ι`. This is the converse of
  the Library's `PointFiberArtinianLifting.isFormallyVersalAt_restrictBundle`.
  Proof: take a lifting problem with point `y = (b', d)`. The spectrum of the
  local Artinian ring `B` has one point, and its residue map is `p ≫ ι`. So the
  range of `b'` lies in the range of `ι`, and `b'` factors as `g ≫ ι` through
  `IsOpenImmersion.lift`. The point `(g, c⁻¹ ≪≫ d)`, with `c` the Library's
  `PseudofunctorPointFiberAtlasRestriction.atlasComparison`, is a point for the
  restricted bundle. Its residue map is `p`, by cancelling the monomorphism `ι`.
  Lift it with `h`, apply the Library's `mapPoints`, and use `mapPoints_restrict`.

## Provenance

This is internal infrastructure. It contains only pseudofunctor coherence and the
one-point topology of local Artinian spectra, and makes no literature assertion.
The second proof follows the published proof of
`isFormallyVersalAt_restrictBundle` in the opposite direction.
