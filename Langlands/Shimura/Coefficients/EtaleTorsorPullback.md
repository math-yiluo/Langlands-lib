# Actual base change of finite geometric etale torsors

Author: Worker 13.

This is an internal geometric prerequisite for comparing associated coefficient
sheaves with their restrictions. It constructs base change of the actual cover
and action and proves that the existing finite geometric torsor condition is
preserved. Its input is a genuine scheme morphism and cover action; it accepts
no output torsor, associated sheaf, or base-change comparison.

The schemes `X` and `Z` and the carrier of the abstract group `G` use universe
`u`. The base morphism `f : Z ⟶ X` is arbitrary. In particular it need not be
etale. The original cover is `Y : Action X.Etale G`, so its structure morphism
`p : Y.V.left ⟶ X` is etale. The pulled-back structure morphism is etale by
stability under base change. No coefficient ring or representation occurs in
this construction.

`etaleObjectPullback f` is Mathlib's morphism-property over-category pullback
functor for the etale property and unrestricted morphisms. At an object `U`
it is the actual scheme fiber product with structure morphism
`pullback.snd U.hom f`. On a map it is the map of fiber products determined by
the original map on the first coordinate and the unchanged second coordinate.
The functor exists for arbitrary `f` because schemes have the required
pullbacks and etale morphisms are stable under base change.

`etaleTorsorPullbackFunctor f G` applies this functor to categorical group
actions using `Functor.mapAction`. Its underlying cover is
`Y.V.left ×[X] Z`. Its action on a deck element `g` has first coordinate the
original deck map after the first projection and second coordinate the second
projection. Its equivariant cover maps have the corresponding coordinate
formulas. The declarations with suffixes `_obj_hom`, `_ρ_fst`, `_ρ_snd`,
`_map_fst`, and `_map_snd` prove these statements. Identity, composition, the
group action laws, and equivariance of the image maps follow from the actual
functor and `mapAction`; none is an additional hypothesis.

`IsFiniteGeometricTorsor.pullback` proves preservation of the existing
predicate in `Coefficients.Etale`. That predicate requires that `G` is finite,
that the cover morphism is finite and surjective, and that its action is free
and transitive on lifts of geometric points over every separably closed field
in universe `u`. Its geometric condition is the following: for two maps `a`
and `b` from the spectrum of that field into the cover with the same image in
the base, there exists a unique `g : G` such that `a ≫ deck(g) = b`.

The proof retains the original finiteness of `G`. Mathlib's base-change
instances give finiteness and surjectivity of the second projection. For two
geometric lifts in the new cover, equality of their second coordinates implies
equality of the images in `X` of their first coordinates, by the fiber-product
square. The original torsor condition therefore supplies a unique deck
element on the first coordinates. The constructed deck action fixes the
second coordinate, so the universal property of the scheme pullback upgrades
this to equality of the two maps into the new cover. Composing any competing
equality with the first projection gives uniqueness from the original torsor
condition. This uses actual morphisms from spectra, and asserts no globally
constant deck element for arbitrary disconnected test schemes.

For `g : V ⟶ Z`, `etaleTorsorPullbackComp f G g` gives the natural isomorphism
from base change along `g ≫ f` to base change along `f` followed by base change
along `g`. It is the canonical fiber-product comparison
`MorphismProperty.Over.pullbackComp`, transported through group actions by
`Functor.mapActionCongr` and `Functor.mapActionComp`. Its components are
therefore equivariant isomorphisms, natural in all original equivariant cover
maps. This module does not assert additional identity or higher coherence
formulas for this comparison.

For any category `I` with object universe `uI` and morphism universe `vI`, and
any group diagram `D : I ⥤ GrpCat.{u}`, `etaleTorsorDiagramPullback f D`
constructs base change of the entire category of varying-group cover diagrams.
It applies the same geometric functor to every object, action, transition,
and diagram morphism by `EquivariantDiagram.mapFunctor`. The original group
diagram `D` is retained. The `_action` and `_transition_hom` equations identify
the individual pulled-back actions and maps. The final
`_isFiniteGeometricTorsor` theorem proves that every original finite geometric
torsor remains one at the same index. The diagram laws and transition
equivariance are constructed by the functor, with no restriction of
transitions to isomorphisms or constant groups.

The provenance is internal: this module applies the published project's actual
torsor predicate to Mathlib's actual scheme pullback functor and proves its
stability by the fiber-product universal property. It claims no new theorem
from Harris or Berkovich. Its Mathlib dependencies are
`CategoryTheory/MorphismProperty/OverAdjunction.lean` (the over-category
pullback and composition comparison), `CategoryTheory/Action/Basic.lean`
(functors on actions), `AlgebraicGeometry/Morphisms/Finite.lean` (finite
base change), and `AlgebraicGeometry/PullbackCarrier.lean` (surjective base
change), at commit `5ed2965256430c3649e86755f9576b54eca72435`, Lean 4.34.0.
The project dependencies are `Coefficients.Etale` and
`CategoryTheory.EquivariantDiagramFunctor`.

Actual Harris Shimura schemes and level torsors remain inputs to be
constructed in their assigned geometric branch. Comparing the associated
sheaf of this pulled-back torsor with an etale restriction, or constructing
inverse image for an arbitrary non-etale base morphism, is a further
obligation. No associated-sheaf, derived-cohomology, compact-support, trace,
coefficient-change, or uniformization comparison is proved here.
