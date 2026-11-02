# Linear-system morphisms under line-bundle isomorphisms

Let `L` and `M` be actual line bundles on a scheme `X`, and let
`e : L.obj ≅ M.obj` be an isomorphism of their module sheaves.
`mapIsoSections e s` transports an ordered family of `n+1` global sections
by applying `e.hom` on the whole scheme to each section. No choice of
trivialization, scalar ring, or basis is part of this operation.

If the sections `s` have no common zero at any point, the transported
sections also have no common zero. The proof converts nonvanishing to
membership in the whole frame open and uses
`Picard.trivializationOpen_mapIso` to identify those opens.

For every scheme map `g : T ⟶ X` landing in the frame open of a section
`s₀`, `sectionRatio_mapIso` says that the ratio of the images of `σ` and
`s₀` equals the original ratio along `g`. Pullback-section naturality
transports the identity expressing `σ` as its unique coefficient times
the frame `s₀`; uniqueness of this coefficient proves the assertion.

For any commutative ring `K` and structure morphism `p : X ⟶ Spec K`,
`pointMap_mapIso` identifies the corresponding actual polynomial-Proj
chart morphisms. Polynomial ring-homomorphism extensionality compares
their constants, which come from the same structure map, and their
variables, whose values are the section ratios just compared.
`linearSystemMap_mapIso` then identifies the two actual scheme maps
`X ⟶ ProjectiveSpace K n` by restricting to the original frame-open
cover. The ordered sections are transported exactly; they are not
identified only up to a permutation or a change of basis.

For any scheme base `S` and map `p : X ⟶ S`,
`relativeLinearSystemMap_mapIso` gives the same invariance for the actual
maps into `RelativeProjectiveSpace S n`. Equality follows from the two
projections defining relative projective space: the base projection is
`p`, and the integral projection is the polynomial linear-system map
over the lifted integers.

This is a derived internal construction using
`LinearSystem.RelativeMorphism`, `Picard.AmpleIsoProof`, and
`Modules.SectionVanishingTransportProof`. The implemented arguments use
their actual line-bundle frame opens, pullback operations, coefficient
uniqueness, and open-cover gluing. No new assertion from external
literature is used. This module establishes invariance under bundle
isomorphisms; it supplies no representability or immersion conclusion.
