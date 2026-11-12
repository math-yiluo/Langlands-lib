# Universal closedness reflected through a surjective source cover

This internal unit supplies the topological reflection step for the host
properness argument. It uses the published point topologies and the actual
presheaf pullbacks throughout. No finiteness or affine-base hypothesis is
needed in these comparisons.

`sourceCoverFibreMap a f y` maps the fibre of the composite `a ≫ f` into the
fibre of `f` over the same test. The map keeps the projection to the test
presheaf. The pullback-pasting lemma identifies its square with a base change
of `a`; consequently a represented geometrically surjective `a` induces a
represented geometrically surjective fibre map.

`isClosedMap_points_schemeYoneda` transports a scheme's closed-map property
to its represented presheaf point spaces through `schemePointsHomeomorph`.
The point-map naturality formula identifies the transported map with the
actual Yoneda point map. `isUniversallyClosedMorphism_of_relative` uses a
represented scheme pullback for each test and transports closedness through
its pullback isomorphism. Its hypothesis is the relative scheme property
`UniversallyClosed`; its conclusion is the published point-topology predicate
`IsUniversallyClosedMorphism`. Specialization gives
`isUniversallyClosedMorphism_schemeToSpace` for every universally closed
scheme morphism over the base.

`IsUniversallyClosedMorphism.of_surjective_comp` proves reflection: for
algebraic-space maps `a : W → X` and `f : X → Y`, represented geometric
surjectivity of `a` and universal closedness of `a ≫ f` imply universal
closedness of `f`. At a scheme test of Y, the actual fibre map is surjective
on quotient point sets. It is continuous because its target is the actual
fibre-product algebraic space, hence has a surjective etale atlas; the atlas
is transported along the whole-presheaf pullback comparison. For a closed set
C in the target fibre, take its closed inverse image under this continuous
map. Universal closedness of the composite makes its image in the test closed.
Surjectivity identifies that image with the image of C, proving the claim.

Finally, `isUniversallyClosed_structural_of_scheme_cover` applies this
reflection to a represented surjective map from a scheme U/S to X/S, when
U's structural morphism is universally closed. The composite to the base is
the Yoneda image of U's structure map by terminality of the base presheaf.
A proper scheme source therefore supplies this hypothesis by its ordinary
scheme universal closedness. The result does not assert existence of the
scheme cover.

The provenance is internal: pullback pasting and relative-property base-change
stability, the published actual algebraic-space fibre products, continuity and
surjectivity of point maps, represented scheme point homeomorphisms and
isomorphism transport. These comparisons do not assume properness descent.
The scheme-cover existence theorem, descent of a chosen cover and its map,
target-atlas comparisons, and the full eight-property limit theorem remain
separate obligations of the host proof.
