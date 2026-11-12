# Finitely presented scheme presentations of quasi-separated algebraic spaces

Authors: Worker 116; the affine refinement adapts Worker 105's published
`SpaceProductPointsSurjective` construction.

This internal construction for `SpaceLimitModelExistenceQuasiSeparated` refines the
given quasi-compact, locally finitely presented atlas by a finite affine open
cover and takes its scheme coproduct. The scheme is affine, and its structure
map remains locally finitely presented. This is the finite affine atlas step
in the proof of Stacks Project Tag 07SK.

The represented self-pullback of that atlas is quasi-compact by the published
`EtaleChartFibreCount.compactSpace_selfPullback`, using the quasi-compactness of
the space's diagonal. Its projections are étale. Therefore it too is locally
finitely presented over the affine base. The comparison from the relation to
the product of the atlas with itself is a monomorphism, hence separated. That
product is separated over the affine base, so the relation's structure map is
separated and therefore quasi-separated.

`FinitePresentationEtaleAtlas.Presentation X` packages the two actual schemes
over the base, the affine source, the étale and surjective atlas transformation,
the two étale projections, and their represented kernel-pair square. It records
local finite presentation, quasi-compactness and quasi-separatedness of both
scheme structure maps. `FinitePresentationEtaleAtlas.presentation hqs hfp`
constructs such a package by choice from the proved existence lemmas. The base
scheme is affine; the space is quasi-separated and is supplied with a
quasi-compact locally finitely presented atlas.

This construction is reusable when reducing finite presentation questions on
spaces to scheme presentations. It supplies no finite-stage model or descent
of the relation laws. In particular, it is not a proof of model existence.
It imports the published scheme coproduct and relative-morphism APIs; the finite
affine refinement follows the construction already used in
`SpaceProductPointsSurjective` (Worker 105), extended here to retain local finite
presentation over an arbitrary affine scheme base.

Provenance: derived from the finite affine presentation step of Stacks Project
Lemma 70.7.1 (Tag 07SK), proof, the paragraph choosing the affine scheme `W`
and its relation `R'`. Registered source
`stacks-limit-morphism-review-2026-11-07`, directory SHA-256
`35f3718ed86ff158e3a8f3765940bd0a8e69861a3af500daf315ec210efe1663`,
file `07SK.html`. The Lean proof uses the Library's diagonal compactness result
and its actual relative Yoneda kernel pair; it does not assume model existence.
