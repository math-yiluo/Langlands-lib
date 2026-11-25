# Fixed pinned comparison existence on arbitrary common schemes

This derived construction assumes the exact affine pinned
Isomorphism Theorem proposition and extends it to actual fixed comparisons
of supplied affine pinned models over every common scheme. It keeps one
specified based full root-datum map throughout. The source setting is Conrad,
*Reductive group schemes* (2014), Theorem 6.1.17, p.197; the affine theorem
remains an explicit input.

The character-monomial formula on every test determines the entire actual
coordinate torus isomorphism: test the individual coordinate exponent
vectors. Thus an exact affine pinned solution has the prescribed fixed
torus square. Its differential equations give equality of the actual
pinning points on the original coefficient ring. Precomposition by the
model-independent dual coefficient map and naturality of the actual pinning
points extend this equality to every affine coefficient test. The result
is `fixedAffineComparison`, carrying both fixed predicates.

For an arbitrary scheme `T`, each morphism to an original affine model base
factors through `T.toSpecΓ : T → Spec Γ(T, ⊤)`. The factor is obtained from
the map on global functions and the target's affine isomorphism. Recover
the two original-ring algebra structures on `Γ(T, ⊤)`, apply the affine
construction there, and pull its fixed comparison back to `T` with the
specified endpoint equalities. No affineness or connectedness assumption
on `T` is needed.

`fixedComparison` chooses this actual comparison. The already proved
arbitrary-scheme fixed rigidity theorem gives its uniqueness and shows
that its normalized pullback along every map of common test schemes is
the corresponding canonical fixed comparison. This provides actual
existence and naturality conditional only on the supplied affine theorem;
atlas compatibility and the parent theorem's global structural data are
separate uses of the construction.
