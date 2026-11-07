# Artinian lifting for representing schemes of versal point fibres

This module connects the Library's formal versality of actual Picard families
(`ArtinianChartVersality.IsFormallyVersalAt`) with smoothness of the schemes
that represent actual point fibres. It is the translation step between the
Artinian lifting criterion `ArtinianLiftingSmooth.smooth_of_liftsArtinian` and
the test reduction `PointFiberProperty.of_finiteTypeAffine`.

Namespace: `Langlands.AlgebraicGeometry.Picard.PicardGroupoid.PointFiberArtinianLifting`.

## Setting

`R : Type u` is a commutative ring and `f : X ⟶ Spec R` a morphism of schemes.
`U : Over (Spec R)` carries an actual line bundle `L` on `(relativeSpace f).obj U`.
For a test `T : Over (Spec R)` and an actual line bundle `M` on
`(relativeSpace f).obj T`, the scheme `P : Over T.left` represents the actual
point fibre through an isomorphism
`e : schemeYoneda T.left P ≅ pointFiberPresheaf f L M`.

## Moving points along the representation

- `sliceIso b : T.iteratedSliceBackward.obj (Over.mk b.left) ≅ Over.mk b` for
  an arrow `b : W ⟶ T` in `Over (Spec R)`. Its components are identities.
- `toPresheaf z` regards a raw fibre point as an element of
  `pointFiberPresheaf f L M`.
- `pointOf f L e b α hα`: for `α : W.left ⟶ P.left` with `α ≫ P.hom = b.left`,
  the fibre point over `Over.mk b` given by `e` applied to `α`, restricted along
  `(sliceIso b).inv`.
- `mapOf f L e a x`: for a fibre point `x` over `Over.mk a`, the arrow
  `Over.mk a.left ⟶ P` given by `e⁻¹` applied to `x` restricted along
  `(sliceIso a).hom`.
- `map_mapOf`: let `r : W' ⟶ W`. If `x` restricts along `r` to
  `pointOf f L e (r ≫ a) α hα`, then `r.left ≫ (mapOf f L e a x).left = α`. The
  proof uses naturality of `e⁻¹`, `PseudofunctorPointFiber.restrict_comp` and
  `restrict_id`, and the identity
  `T.iteratedSliceBackward.map r' ≫ (sliceIso a).hom = (sliceIso (r ≫ a)).hom ≫ r`
  of slice arrows.

## Main theorems

`liftsArtinian_of_versal f L e hV` assumes `P.hom` and `T.hom` locally of finite
type. Its hypothesis `hV` says: for every field `K : Type u` with an
`R`-algebra structure and every `p : ArtinianTest.residueBase R K ⟶ U` with
`p.left` locally of finite type, `IsFormallyVersalAt f L p` holds. The
conclusion is `ArtinianLiftingSmooth.LiftsArtinian P.hom`.

Proof. Take a lifting problem: local Artinian `B'`, `B`, an elementary
surjection `φ : B' → B`, `α : Spec B ⟶ P.left` and `β : Spec B' ⟶ T.left`, with
`α ≫ P.hom = Spec φ ≫ β` and residue point of `α` locally of finite type.

1. `Spec.preimage (β ≫ T.hom)` makes `B'` an `R`-algebra, and `B` an `R`-algebra
   through `φ`. With `K = ResidueField B` and the residue augmentations,
   `ArtinianTest.mk` gives tests `A` (on `B'`) and `Bt` (on `B`), and
   `ArtinianTest.homMk φ` a surjective test arrow `q : A ⟶ Bt`.
2. `a = Over.homMk β : base A ⟶ T` and `b = baseMap q ≫ a`. The point
   `y = pointOf f L e b α` lies over `Over.mk b`.
3. Put `p = reduction Bt ≫ y.1`. Then `p.left ≫ U.hom` is the structure map of
   `Spec K` over `Spec R`. That map equals the residue point of `α` followed by
   `P.hom` and `T.hom`, so it is locally of finite type. By
   `locallyOfFiniteType_of_comp`, `p.left` is locally of finite type.
4. `hV` gives versality at `p`. Applied to `q`, with `y` (whose residue map is
   `p` by definition), it gives `x` over `Over.mk a` restricting to `y`.
5. `γ = (mapOf f L e a x).left` satisfies `γ ≫ P.hom = β` by `Over.w`, and
   `Spec φ ≫ γ = α` by `map_mapOf`.

`pointFiberProperty_smooth_of_versal f L hV T M` assumes `R` noetherian, `f`
proper, flat and locally of finite presentation, and `U.hom` locally of finite
type, with `hV` as above. It proves `PointFiberProperty f L @Smooth T M` for
every test `T` and bundle `M`. `PointFiberProperty.of_finiteTypeAffine` reduces
the claim to `affineBase R B` with `B` of finite type over `R`. There `B` is
noetherian and `U.hom` is locally of finite presentation. The published
`exists_locallyOfFinitePresentation_pointFiberScheme` gives a representing
scheme whose structure map is locally of finite presentation.
`liftsArtinian_of_versal` and `smooth_of_liftsArtinian` then make it smooth.

`exists_smooth_pointFiberScheme_of_versal` gives, under the same hypotheses,
for every `T` and `M` a representing scheme `P` with `Smooth P.hom`. It uses the
published `hasAffinePointFiberSchemes`.

## Restricting the family

`isFormallyVersalAt_restrictBundle f L ι p h` uses the published
`restrictBundle f L ι`, the ordinary pullback of `L` along
`(relativeSpace f).map ι` for `ι : V ⟶ U` in `Over (Spec R)`. It assumes that
`ι.left` is an open immersion and that `L` is formally versal at `p ≫ ι`. It
concludes that `restrictBundle f L ι` is formally versal at `p`.

Proof. The published
`PseudofunctorPointFiberAtlasRestriction.mapPoints` composes the base map of a
point with `ι`. It sends a lifting problem for the restricted family to one for
`L`, and versality of `L` at `p ≫ ι` gives a lift `⟨a', d'⟩`. The spectrum of a
local Artinian ring has one point, and that point maps into the image of `p`
(`ArtinianChartVersality.residueMap_of_restrict_eq`). So `a'` factors as
`g ≫ ι` (`IsOpenImmersion.lift`). Then `⟨g, (atlasComparison g)⁻¹ ≪≫ d'⟩` is a
point for the restricted family, and `mapPoints` sends it to `⟨a', d'⟩`. Its
restriction is the prescribed point, because `mapPoints` commutes with
restriction (`mapPoints_restrict`) and is injective (`mapPoints_injective`; `ι`
is a monomorphism by `Over.mono_of_mono_left`).

## Provenance

Internal infrastructure for the finite-type Picard stack atlas task. It follows
the standard step that versality at finite-type points makes the chart smooth
over finite-type tests (The Stacks Project, Artin's Axioms, Lemma 98.13.3,
Tag 07XT, and Lemma 98.13.7, Tag 07XX, artin.pdf pp. 22–23, in snapshot
`stacks-artin-axioms-approximation-2026-11-06`). It uses the Library's lifting
conventions and the variant criterion `smooth_of_liftsArtinian`. No cited source
theorem is formalized in this module.
