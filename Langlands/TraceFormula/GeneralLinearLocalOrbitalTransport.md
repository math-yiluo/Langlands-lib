# Local orbital nonvanishing from the matrix model of `GL_n(K_v)`

For a finite place `v` of a number field `K`, `localMatrixHomeomorph K n v` is the Library's
identification `localGLHomeomorph` of the local points of the group scheme `GL_n` at `v` with
the matrix group `GL_n(K_v)` of the completion `v.adicCompletion K`. `placeOne_apply` shows
that the local twist of the identity automorphism is the identity.

`localOrbitalNonvanishingAt_of_matrix` transports orbital nonvanishing from the matrix group
to the group-scheme points. Let `x` be a local point whose image `γ` in `GL_n(K_v)` is regular
semisimple, and suppose the orbital integral of `φ` at `γ` is nonzero for every Haar measure
on `GL_n(K_v)`, every right Haar measure on the centralizer of `γ` and every compatible
quotient measure. Then `LocalOrbitalNonvanishingAt K GLₙ v x (φ ∘ localMatrixHomeomorph K n v)`
holds.

The proof obtains compatible measures on the matrix side from `orbitalMeasureExistence`
(regular semisimple centralizers are tori). It pushes them forward along the inverse
homeomorphism, which preserves Haar measures and compatibility
(`isCompatible_map_twistedOrbit`), and changes variables in the orbital integral
(`integrable_and_twistedOrbitalIntegral_map_equiv`).
