# Finite homomorphisms from tori onto their actual images

`Langlands.GroupScheme.FiniteTorusImageStatement.{u}` concerns every field
`k : Type u`, every actual torus `T`, every affine group scheme `H` locally
of finite type over `k`, and every finite homomorphism `f : T ⟶ H`.
Its actual schematic image `SchematicImage.image f` is a torus, its
canonical inclusion is closed, and its canonical projection is an isogeny:
a finite, flat, surjective homomorphism. The two maps compose to `f`.
If `T` is split, the actual image is split as well.

The proposition retains arbitrary characteristic and imperfect fields.
It does not assume smoothness, connectedness or reductivity of `H`,
separability of `f`, or a positive torus rank.
The theorem `finiteTorusImageStatement` proves the displayed proposition.

## Implemented proof and helper interfaces

`IsTorus.isIsogeny_schematicImageProjection` first installs the actual torus's
affineness, smoothness and connectedness. The published
`smoothConnectedAffineGeometry` theorem supplies its geometric integrality.
The schematic-image projection is flat and surjective by the published
`HomImage.flat_projection` and `HomImage.surjective_projection` lemmas.
Its composite with the closed image inclusion is the original finite
homomorphism. The scheme lemma `IsFinite.of_comp` therefore makes the
projection finite. These three properties give precisely `IsIsogeny`;
no assertion about surjectivity of its differential is made.

The image's torus property is the existing
`IsTorus.isTorus_schematicImage` theorem.
`IsSplitTorus.isSplitTorus_schematicImage` applies the published
`IsSplitTorus.of_schematicallyDominant_hom` theorem to the actual projection,
which is schematically dominant by construction. This split-image helper
needs only an affine target and a quasi-compact original homomorphism;
it does not need finiteness or local finite type of the target.

`IsTorus.exists_isogeny_finiteHomImage` applies the first helper to `i ≫ q`,
where `i : T ⟶ G` is any closed torus embedding and `q : G ⟶ H` is finite.
Closed immersions and finite morphisms compose to a finite morphism, giving
an actual isogeny from `T` onto its image in `H`. It returns the image as a
commutative group scheme, its closed inclusion, the isogeny, their commuting
square and the split-image implication. No maximality, centrality,
splitness, or geometric assumption on `G` is required.

## Provenance and scope

This is a derived composition of published actual torus-image, geometric
integrality, image-flatness, schematic-dominance and scheme-finiteness
interfaces. It makes no new external structural assertion. The result
provides a restriction API for the Cartan-generation isogeny construction.
It does not construct lifts of target tori or prove the structural
semisimple reduction or the final Cartan-generation proposition.
