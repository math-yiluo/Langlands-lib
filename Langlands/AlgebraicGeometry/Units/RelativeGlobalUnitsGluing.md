# Extending representation of relative units from affine tests

This internal helper is derived from the actual relative global-unit construction and Mathlib's scheme gluing and open-cover APIs. It introduces no geometric hypotheses on the base, the family, or the test scheme.

Units of the global functions on the relative fibre product are determined on the base change of any open cover of the test scheme. This follows from the separatedness of the structure sheaf and injectivity of the map from units to their underlying functions.

For a fixed universal unit, injectivity of its pullback map on affine tests implies injectivity on every test scheme. Restrict two morphisms to an affine cover, use affine injectivity and functoriality of restriction there, and apply uniqueness of scheme morphisms on an open cover.

Surjectivity is also local. Choose a preimage of the given unit on each affine cover member. Their restrictions to each pairwise overlap agree by the global injectivity already proved. Glue these scheme morphisms, check that the glued morphism is over the base on the cover, and check its pulled-back unit on the induced open cover of the fibre product. This argument uses no quasi-compactness, separatedness, or reducedness assumptions.

`fromUniversalUnit_isIso_of_affine` packages this result for the exact canonical natural transformation of lifted presheaves defined by the universal unit. The lifts change neither injectivity nor surjectivity. The components are therefore isomorphisms of types, which makes the natural transformation an isomorphism. The result is conditional on affine bijectivity; it does not assert that arbitrary families or universal units are representable.

`fromUniversalUnitIsoOfAffine` is the resulting actual presheaf isomorphism. Its forward map is definitionally `fromUniversalUnit f U a`, recorded by `fromUniversalUnitIsoOfAffine_hom`. Every declaration preserves the arbitrary universe parameter `u`. In particular, no nonemptiness assumption is imposed on the test scheme or its cover. This helper supplies the gluing step of the finite-algebra unit argument; the affine bijectivity and smoothness results are separate inputs to that application.
