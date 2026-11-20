# Group structure on a faithfully flat schematic image

Let `f` be a group-scheme homomorphism over a scheme `S`. Assume its
underlying morphism is quasi-compact and that the canonical projection to
its schematic image is flat and surjective. The schematic image carries
a group law, and the canonical projection and closed inclusion are group
homomorphisms whose composite is `f`. If the source is commutative,
`commGroup` equips the same image with a commutative group structure.

The product of the projection with itself over `S` is quasi-compact,
flat and surjective by stability under composition and base change.
In particular this product is schematically dominant. The ambient
multiplication restricts to the image by closed factorization along this
product, and inversion restricts by the same argument along the
projection. The unit factors via the source unit. `grpObjOfMono` checks
the group axioms by cancellation at the image inclusion, which also
detects compatibility of the projection with the group law.
Commutativity follows by precomposing with the product of the projection
with itself, an epimorphism by flatness and surjectivity, and applying
commutativity in the source.

This internal construction uses the Library's scheme-theoretic image and
group-object restriction APIs. It supplies the group structure for the
arbitrary-base torus image argument.
