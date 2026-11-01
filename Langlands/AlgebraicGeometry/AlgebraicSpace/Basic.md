# Algebraic spaces over an arbitrary scheme

Authors: Worker 147 and Worker 133.

This module defines algebraic spaces over every `S : Scheme.{u}` using the Stacks
Project fppf-sheaf convention. An object is an actual fppf sheaf on schemes over
`S`, with representable diagonal and a representable, geometrically surjective
etale atlas by an actual scheme over `S`. There is no quasi-compactness condition
on the diagonal. In particular, the definition assumes no quasi-separatedness,
noetherianity or reducedness of the base.

## Sources and convention

The source is the registered retained HTML snapshot
`stacks-algebraic-spaces-foundations-2026-11-01`, downloaded 1 November 2026. Its
permanent Stacks references are:

- [Section 65.3, Tag 025U](https://stacks.math.columbia.edu/tag/025U):
  representable transformations of functors on actual schemes.
- [Definition 65.5.1, Tag 025V](https://stacks.math.columbia.edu/tag/025V):
  properties of a representable transformation, tested on represented scheme
  projections after every base change from a scheme.
- [Remark 65.5.2, Tag 02YN](https://stacks.math.columbia.edu/tag/02YN):
  geometric surjectivity differs from surjectivity as a presheaf or sheaf map.
- [Lemma 65.5.10, Tag 025W](https://stacks.math.columbia.edu/tag/025W):
  a representable diagonal makes every map from a scheme representable.
- [Definition 65.6.1, Tag 025Y](https://stacks.math.columbia.edu/tag/025Y):
  the fppf sheaf, representable diagonal and surjective etale atlas conditions.
- [Lemma 65.6.2, Tag 025Z](https://stacks.math.columbia.edu/tag/025Z):
  schemes give algebraic spaces.
- [Section 65.6, Tag 025X](https://stacks.math.columbia.edu/tag/025X), including
  Definition 65.6.3: morphisms are transformations of functors; the discussion
  distinguishes conventions and omits the quasi-compact-diagonal axiom.

The retained pages and their comments were read. Source-specific errata notes
were absent in the project, current Library and workspace locations checked by
the authors. No equivalence with an etale-sheaf convention is asserted here.

## Actual sheaves and universes

All names below are in `Langlands.AlgebraicGeometry.AlgebraicSpace`, except for
the type `Langlands.AlgebraicGeometry.AlgebraicSpace` itself.

`Presheaf S` is precisely `(Over S)ᵒᵖ ⥤ Type (u + 1)`. The topology
`fppfTopology S` is Mathlib's `Scheme.fppfTopology.over S`, the actual induced
slice Grothendieck topology. `FppfSheaf S` is the actual category
`Sheaf (fppfTopology S) (Type (u + 1))`, so its objects carry the corresponding
sheaf condition. These definitions do not replace a sheaf condition by an
uninterpreted predicate.

`schemeYoneda S` is `CategoryTheory.uliftYoneda.{u + 1}`. For actual
`T U : Over (S : Scheme.{u})`, its value on `U` at `op T` is
`ULift.{u + 1} (T ⟶ U)`. Morphisms `T ⟶ U` are actual morphisms of schemes over
`S`, in `Type u`. The lift puts their functor of points in `Type (u + 1)`, since
`max u (u + 1) = u + 1`. Pullback is induced by precomposition with the actual
morphism over `S`, followed by this same lift. All test and representing schemes
remain in `Scheme.{u}`; neither the base nor the quantification over actual
schemes is enlarged.

This value universe accommodates the Library's existing
`RigidifiedLineBundle.classPresheaf` directly. The module neither changes that
presheaf nor adds a smallness hypothesis to a prospective Picard functor. It
imports no Picard construction and assumes no universe-resizing axiom.

`schemeSheaf S` uses `GrothendieckTopology.uliftYoneda` on this slice topology.
Mathlib proves that `Scheme.fppfTopology` is subcanonical; the imported
`Sites.SubcanonicalOver` transfers subcanonicity to the slice. The underlying
presheaf of `schemeSheaf S` is the displayed lifted functor of points.

## Represented transformations and geometric properties

For actual presheaves `F G : Presheaf S` and `f : F ⟶ G`,
`IsRepresentableMorphism f` is exactly
`(schemeYoneda S).relativelyRepresentable f`. Expanded, it says that for every
actual `U : Over S` and `g : (schemeYoneda S).obj U ⟶ G`, there exist an actual
`V : Over S`, `p : V ⟶ U`, and `a : (schemeYoneda S).obj V ⟶ F` such that
`IsPullback a ((schemeYoneda S).map p) f g` holds in the category of actual
presheaves. Thus the representation includes the pullback universal property.

For a witness `hf`, `hf.pullback g`, `hf.snd g`, `hf.fst g`, and
`hf.isPullback g` in namespace `IsRepresentableMorphism` transparently expose
Mathlib's chosen representing scheme, actual projection over `S`, first
presheaf projection and universal property. These are aliases of the existing
relative-representability API, with no new choice of representability notion.

`IsEtale f` is `MorphismProperty.relative` applied to `schemeYoneda S` and the
inverse image of the actual scheme property `AlgebraicGeometry.Etale` under
`Over.forget S`. It includes representability and says that, in every represented
pullback square just described, `Etale p.left` holds. `IsSurjective f` is the
same construction with `AlgebraicGeometry.Surjective`; it includes
representability and requires `Surjective p.left` in every such square.
Here `p.left : V.left ⟶ U.left` is an actual scheme morphism, and surjectivity
means surjectivity of its underlying map of points. There is no objectwise
surjectivity condition on `f.app`, and no identification with sheaf surjectivity.

`IsEtale.representable` and `IsSurjective.representable` expose the
representability conjuncts. Their `projection` lemmas expose the actual scheme
properties for any represented pullback square, rather than only a selected one.
The proofs are projections of the defining Mathlib conjunctions.

## Objects, morphisms and evaluation

`HasRepresentableDiagonal F` means `IsRepresentableMorphism (Limits.diag F)`.
The product and diagonal are those in the actual presheaf category.
`IsAlgebraicSpace S F`, for `F : FppfSheaf S`, asserts this condition on `F.obj`
and the existence of an actual `U : Over S` and
`a : (schemeYoneda S).obj U ⟶ F.obj` satisfying both `IsEtale a` and
`IsSurjective a`. Each of these properties already includes representability,
so the atlas condition supplies a representable map.

`AlgebraicSpace S` is the full subcategory of `FppfSheaf S` cut out by
`IsAlgebraicSpace S`. Its category structure is inherited from Mathlib's full
subcategory category. `hom`, `homMk`, and `homEquiv` identify its morphisms with
all actual natural transformations of the underlying presheaves, equivalently
of the actual sheaves. The two inverse laws of `homEquiv` are definitional.
Identity, composition and category laws are inherited from natural
transformations; no additional morphism condition is imposed.

`toSheaf`, `presheaf`, `forgetToSheaf` and `forgetToPresheaf` expose the actual
underlying objects and morphisms. `sections X T` is evaluation at `op T`, and
`pullback X f` is the presheaf map along `f.op`. `pullback_id` and
`pullback_comp` are the corresponding functor laws on elements. `mapSections`
evaluates a morphism of spaces on sections, and `mapSections_naturality` is the
naturality equation on elements; these proofs apply Mathlib's functor laws and
natural-transformation naturality.

`hasRepresentableDiagonal X` exposes an object's diagonal condition.
`representable_from_scheme X a` is the convenience consequence of Tag 025W,
obtained by applying Mathlib's `Functor.relativelyRepresentable.of_diag` to
that condition. `exists_atlas X` exposes an actual atlas and its
representability, etaleness and geometric surjectivity proofs, by extracting the
object's defining witnesses.

## Schemes and the additional scheme-representability property

`scheme_hasRepresentableDiagonal U` proves the diagonal condition for an actual
scheme's lifted functor of points. Its implemented proof uses
`Functor.relativelyRepresentable.diag_of_map_from_obj`: full faithfulness of
lifted Yoneda turns any map between represented presheaves into an actual map of
schemes over `S`, and actual pullbacks in `Over S`, preserved by lifted Yoneda,
show that this map is representable.

`scheme_isAlgebraicSpace U` combines that diagonal with the identity atlas. For
each base change, the identity of the test scheme gives a represented pullback
square; its projection is etale and surjective. The implementation uses
`MorphismProperty.relative.of_exists`, whose invariance under isomorphisms
transfers these properties to every represented square. For etaleness, the
needed invariance is obtained from Mathlib's base-change stability of etale
scheme morphisms. The sheaf condition is supplied by subcanonicity as above.
These are the elementary categorical constructions corresponding to Tag 025Z.

`schemeToSpace S : Over S ⥤ AlgebraicSpace S` lifts `schemeSheaf S` through the
full subcategory. `schemeToSpaceFullyFaithful S` obtains full faithfulness from
Mathlib's `fullyFaithfulUliftYoneda` for the slice topology and the faithful
forgetful functor to sheaves. The module registers the resulting `Full` and
`Faithful` instances. This is Yoneda full faithfulness for actual schemes over
`S` in the chosen value universe.

Finally, `IsRepresentedByScheme X : Prop` is
`∃ U : Over S, Nonempty ((schemeYoneda S).obj U ≅ X.presheaf)`.
It requires an actual natural isomorphism with the functor of points of an
actual scheme over `S`. The predicate is separate from the definition of an
algebraic space; a future proof may produce its scheme witness. The elementary
`schemeToSpace_isRepresentedByScheme U` supplies the original scheme and the
identity isomorphism for a scheme included as a space.

This contribution contains definitions and the described basic categorical
constructions. It constructs no Picard representer and proves no Artin
representability, Picard smoothness or schemeness theorem.
