# Universal closedness of a scheme mapping to a universally closed space

This internal unit supplies the universal-closedness part of the properness of
a scheme cover U → S in the finite-presentation refinement of the weak Chow
cover (Stacks Project, Lemma 69.18.1, tag 089I; the refinement itself is
derived, see `ProperSchemeCoverStatement.md`). U is a scheme over S with a
represented map a from its presheaf to an algebraic space X/S. When a is
universally closed in the relative scheme sense and the structural morphism of
X is universally closed, the structure map of U is universally closed as a
scheme morphism. All statements use the published point-topology predicate
`IsUniversallyClosedMorphism`, the actual presheaf pullbacks and the actual
fibre-product algebraic spaces.

`Points.isClosedMap_of_atlas_fibres` treats a presheaf map m : F → G, where F
and G each have a surjective étale scheme atlas. If the projection of the
fibre of m over the atlas b of G is closed on points, then m is closed on
points. The proof takes the closed inverse image of a closed set under the
continuous first projection. The pullback image formula
`Points.preimage_image_of_isPullback` identifies the image of that inverse
image with the inverse image under b of the image of the set. The atlas b is
a quotient map on points (`isQuotientMap_chartPointMap`), so the image is
closed.

`IsUniversallyClosedMorphism.isClosedMap_points` applies this to the atlas of
the target: a universally closed morphism of algebraic spaces is closed on
points.

`IsUniversallyClosedMorphism.comp` proves that universally closed morphisms of
algebraic spaces compose. At a scheme test y of the final target, the fibre
of f ≫ g maps to the fibre of g by `sourceCoverFibreMap`. Its fibre over an
atlas of the fibre of g is a base change of f, by pasting with
`sourceCoverFibreMap_isPullback`. Hence that projection is closed on points,
transported along the pullback isomorphism by `Points.isClosedMap_of_iso`.
The previous lemma then makes the fibre map closed on points, and the
projection of the fibre of f ≫ g is its composite with the closed projection
of the fibre of g. The atlases of both fibres are those of the actual
fibre-product algebraic spaces, transported along `FibreProduct.presheafIso`.

`universallyClosed_of_isUniversallyClosedMorphism_schemeToSpace` converts back
to schemes. For a morphism q : U → V of schemes over S, universal closedness
of the induced morphism of algebraic spaces gives Mathlib's
`UniversallyClosed q.left`. For a scheme morphism T' → V the test T' is
regarded over S. The represented pullback of the Yoneda functor gives a
pullback square of schemes over S, which the forgetful functor carries to a
pullback square of schemes. Closedness on presheaf points of the represented
projection is transported along the represented pullback isomorphism. It is
then transported to the underlying topological spaces by
`schemePointsHomeomorph`, using the point-map naturality
`schemePointsTo_map`. Finally the pullback isomorphism identifies the
projection with Mathlib's `pullback.fst`.

`universallyClosed_of_relative_of_structural` is the final statement: for
X : AlgebraicSpace S, U : Over S and a represented map
a : (schemeYoneda S).obj U ⟶ X.presheaf whose pullbacks along all scheme
tests are universally closed, universal closedness of `structuralMorphism X`
gives `UniversallyClosed U.hom`. Indeed `isUniversallyClosedMorphism_of_relative`
makes a universally closed as a morphism of spaces. By terminality of the base
presheaf, the composite with the structural morphism is the image of
U.hom : U → S over S, so the previous two lemmas apply.

The provenance is internal. The arguments are the standard topological
reasoning for universally closed morphisms, carried out with the published
point topologies. Nothing here constructs a cover, uses a limit argument or
assumes properness descent.
