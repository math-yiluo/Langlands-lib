# Actual commutator generation and source descent

This internal adapter works at arbitrary universe `u` over any field `k`, with
actual affine group schemes `G`, `H`, and `K`, an actual commutative acting group
scheme `S`, and group homomorphisms `i : H ⟶ G` and `j : K ⟶ G`.

`exists_generated_commutator` assumes the existing general
`PointedImageGenerationStatement`, smoothness of all three groups, and
connectedness of `H` and `K`. The published
`smoothConnectedAffineGeometry` theorem supplies affineness, finite type, and
geometric integrality of the actual product `H.X ⊗ K.X`. Pointed generation
applies to the actual commutator morphism, expressed as its scheme-theoretic
image factor followed by its closed image inclusion. The distinguished point
is the pair of identities, whose commutator is the identity. The conclusion is
a supplied `GeneratedImage` with `HasSmoothConnectedGeneration`, retaining the
exact geometry and positive dominant-power clauses of that predicate. The image
scheme itself need not be smooth and is not given a group law.

For actual automorphic actions `b`, `c`, and `d` with `i` and `j` equivariant on
every test scheme, `commutator_source_equivariant` proves that the product action
commutes with the actual commutator morphism. If the acting group is a split
torus, `commutator_envelope_stable` then applies the published closed-envelope
stability theorem.

For an already supplied generated representative `D`, `generatedImageFactor`
is the canonical morphism from the actual affine commutator image to
`D.group.X`. It uses `GeneratedImage.sourceFactor` and schematic dominance of
the actual image factor. Its composite with the represented inclusion is
`imageInclusion`, and it sends the actual image origin to the identity.
`generatedImageFactor_power_isDominant` transfers dominance of any original
power of `D` to the corresponding ordered power of the descended factor; it
does not assert existence of a dominant power by itself.

Given stability of the closed envelope, the descended factor is pointed
equivariant for the actual image action and the actual restricted group action.
The proof cancels the represented inclusion and uses its defining action
identity. Every equivariance assertion retains all test schemes.

These are internal applications of published generation, geometry, source
descent, and action interfaces, rather than new original-literature claims.
The general pointed-generation proposition is still an explicit premise of the
existence lemma. This module does not establish the coordinate-to-Lie
comparison, finite-power support bound, or the host
`SemigroupCommutatorStatement`; those remain separate proof obligations.
