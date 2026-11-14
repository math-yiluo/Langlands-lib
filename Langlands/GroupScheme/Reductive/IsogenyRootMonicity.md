# Monicity of finite additive maps of an indivisible root weight

This internal derived unit treats a finite homomorphism from an actual
naturally coordinated additive line to an affine group of finite type over an
arbitrary field. A specified split torus acts on the line with a nonzero
character and on the target by conjugation. The homomorphism is equivariant on
every scheme test. If no integral multiple of the character of degree at least
two is an actual target root, `HomImage.mono_of_noHigherRoots` proves that the
underlying relative-scheme homomorphism is monic.

The proof forms the actual schematic image, which is again an additive line,
and restricts the torus action to it. Single-weight coordinates and universal
additive-polynomial classification give a unit scalar times a characteristic
power monomial for the image projection. The differential of the closed image
inclusion transports a nonzero image tangent vector to a nonzero target weight
vector. Thus its character is an actual root. The absence of higher roots
forces the monomial degree to be one. Such a polynomial is injective on points
over every coefficient algebra, including nonreduced algebras; affine tests
detect equality on arbitrary scheme tests. The image projection and its closed
inclusion are therefore monic, as is their composite.

The preliminary `RelativeRoot.VectorLine.mono_of_polynomial_linear` formalizes
the all-algebra injectivity step for any two supplied natural line coordinate
systems and a unit scalar polynomial.

Provenance is derived from the actual finite additive-line image, restricted
image action, single-weight coordinates, universal polynomial and closed-image
tangent constructions. No injectivity of the original differential is assumed.
This unit does not establish the full root-datum comparison.
