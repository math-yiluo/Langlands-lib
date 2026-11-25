# Small diagrams of pointed affine étale neighbourhoods

Fix a scheme `S` and a morphism `g : Spec Ω ⟶ S` from a field. An object of
the category of elements used here is an affine scheme `Spec A` étale over
`S` together with a lift of `g`. Its morphisms commute with the maps to `S`
and with the lifts. `PointedAffineEtale.Index g` is a small model of this
category in the universe of `S`. The `diagram` and `structural` maps give its
affine schemes over `S`, and `rings` gives the coordinate rings on the
opposite index. The lifts of `g` induce the natural transformation `point`
from the ring diagram to the constant diagram with value `Ω`.

When `Ω` is separably closed, Mathlib gives cofilteredness of the category of
all étale neighbourhoods pointed by `g`. The inclusion of affine stages is
fully faithful. Each pointed étale scheme has an affine open containing the
image of the unique point of `Spec Ω`, so the lift factors through that open.
This gives the cofilteredness criterion for the affine subcategory, which
passes to the small model by equivalence.

In `refinement`, an étale extension of the coordinate ring of a stage with
a compatible map to `Ω` gives a new affine neighbourhood over `S`. The
equivalence with the small model supplies a representative of this
neighbourhood and a transition from the original coordinate ring. The
transition factors through the extension and preserves the chosen map to `Ω`.

For a ring cocone, `spectrumCone` takes its opposite and applies spectrum.
`spectrumConeIsLimit` uses preservation of limits by the spectrum functor
to turn a colimiting ring cocone into a limiting scheme cone. Given
cofilteredness, a common refinement shows the map from the cone to `S` is
independent of the stage. `baseMap_point` shows that a field map out of the
ring cocone point extending the stage maps induces `g` after composing with
that map to `S`.

This construction supplies the indexing and spectrum steps used in
`StrictLocalEtaleLimitExistenceStatement`. It is derived from the category of
pointed étale algebras in [Stacks Project, Algebra, Lemma 10.155.11
(04GW)](https://stacks.math.columbia.edu/tag/04GW). In that lemma a chosen
embedding of the stage residue field into the separable closure gives the
map from the stage algebra to the field. The construction here encodes the
same pointing by a lift of `g` and uses Mathlib's affine étale site and
essential smallness to form the index.
