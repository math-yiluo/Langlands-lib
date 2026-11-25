# Effective torus solutions of pinned Galois data

This internal construction takes fields `k`, `K` in universe `u` with
`K/k` finite Galois, an affine group over `K` with split pinning `p`,
and a supplied based action `ρ`. It supplements the actual torus
datum in `PinnedGaloisTorus` with effective descent and root datum
comparison.

`GaloisTorusSolution` records an effective ambient solution, an actual
commutative torus object over `k`, its compatible comparison over `K`,
the descended inclusion and its recovery equation, connected
reductivity of the ambient group, and affineness of both objects.
`galoisTorusSolution` constructs these data by affine effective descent
of the torus and the published quasi-split descent of the ambient
group. Faithfully flat descent reflects commutativity; compatibility
descends the actual inclusion.

For any such solution, the torus becomes split and maximal over `K`,
by the supplied actual group and torus isomorphisms. The descended
ambient group is affine and locally of finite type.
`RootComparison` and its chosen instance `rootComparison` provide a reduced
root datum of the recovered pair and its comparison with `p.rootDatum`
through the actual isomorphisms. `pinningData` uses exactly the descended
torus and inclusion and maps the given base along that comparison. Root
pinning existence supplies its simple-root vectors. `rootEquiv` preserves
the base and on characters is exactly precomposition with the forward
torus isomorphism; the two corresponding theorems prove these properties.

The provenance is internal: it combines imported affine descent,
commutativity reflection, torus transport, root datum existence,
geometric root datum comparison, and root pinning existence. The
star-action calculation and finite-field cyclic realization are
subsequent obligations.
