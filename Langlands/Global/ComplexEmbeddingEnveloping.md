# The archimedean enveloping center in complex embedding coordinates

For a totally complex number field, `complexEmbeddingCenterInclusion` sends the enveloping center of a complex matrix Lie algebra at a single embedding into the actual global enveloping center. It transports the coordinate inclusion along the enveloping equivalence of `complexEmbeddingLieCoordinates`. The coordinate range theorem for finite products gives `iSup_complexEmbeddingCenterInclusion_range`. The corresponding extensionality theorem compares algebra maps out of the center by testing them on each of these inclusions.

`complexEmbeddingLieInclusion_place` compares the inclusion at each embedding with the actual place inclusion. The proof projects both Lie maps to all embedding coordinates. At the same place it uses the inverse law for the local two-coordinate split, and at every other place the projection is zero. The comparison lifts to the actual enveloping maps by functoriality of the universal enveloping algebra.

This derived interface connects the finite-product center calculation with the local standard-module action and the global highest-weight normalization in the totally complex bridge.
