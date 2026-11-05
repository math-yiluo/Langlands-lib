# Envelope normality from an fpqc subgroup product

This internal unit constructs `subgroupProductConjugationLift`, the actual
factorization of the universal conjugation morphism `N × T → G` through a
represented subgroup `H`. The preceding fpqc transporter lemma gives its
existence, and the representing monomorphism gives uniqueness. Its composite
with `H → G` is proved to be exactly the original conjugation morphism.
The construction works over any base scheme and any commutative group `T`.

The envelope-normality reduction concerns a smooth affine group `G` over a
field. Supply a smooth connected closed split unipotent kernel `N → G`, the
actual represented fppf quotient `q : G → T`, where `T` is a torus, and a
homomorphic section `s`. Also supply subgroups `V,C → N` such that `V` maps
into the fixed torus envelope, `C` centralizes the section, and the actual
multiplication `V × C → N` is flat, surjective and quasi-compact.

The section is a closed subgroup because the ambient affine group is separated.
Its torus image therefore lies in the fixed envelope. The published full-kernel
complement theorem gives an actual multiplication isomorphism `T × N ≅ G`.
Every ambient point thus decomposes on its original test as a section point
times a kernel point. The fpqc subgroup-product transporter puts conjugates
of the section by the kernel point in the envelope. Conjugating further by
the section point preserves the envelope by its subgroup laws. This gives
universal section-conjugate containment. The preceding
`TorusSectionEnvelopeNormality` reduction then proves full normality.

The existing stable-vector subgroup proposition remains an explicit input to
the section-to-normality step; its linearization and torsor inputs use published
proofs. This unit does not establish the supplied structural decomposition or
fpqc product. In the finite-field application, rational factorization and the
separate split-unipotent product criterion are intended to establish that product.
Every containment and equality in the implemented argument holds on arbitrary
relative tests, including nonreduced schemes.
