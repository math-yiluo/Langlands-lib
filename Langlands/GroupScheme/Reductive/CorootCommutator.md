# Inverted cocharacters and local commutators

This internal helper expresses the elementary Weyl-reflection argument used in the torus part of relative semisimple perfectness. If an actual normalizing point acts on an actual cocharacter by inversion, the square of every point in its image is an abstract commutator. The group identity is `[g,n] = g^2` when `n g n^{-1} = g^{-1}`. The cocharacter calculation uses the precise all-test inner-conjugation formula from the supplied normalizer equality.

The single-cover descent helper uses a surjective flat locally finitely presented morphism as a singleton fppf cover. Further refinements are composed using the local commutator descent API.

`IsInvertedByNormalizer` records the existence of such a normalizing base point and torus automorphism. Its `locallyCommutator` theorem applies to arbitrary test schemes: on each affine chart the parameter acquires a square root along the explicit surjective fppf refinement from `UnitPowerExtension.exists_roots_test`; the square is an abstract commutator there. Composing these covers and the affine cover yields the claimed local membership. This criterion makes no reductivity assumption and does not assert that a normalizer exists.
