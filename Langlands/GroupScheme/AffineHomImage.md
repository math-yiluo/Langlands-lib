# The schematic image of an affine group homomorphism

Worker 1280. This internal construction derives a group structure on the
scheme-theoretic image of a homomorphism between affine group schemes over an
arbitrary field. It uses the existing Library lemmas for schematic dominance of
the image projection and its tensor square, factorization through a closed
immersion, and restriction of group objects along a monomorphism.

The underlying scheme is the original morphism's scheme-theoretic image.
The unit factors through the image projection. Multiplication and inversion
factor through the image inclusion after precomposing by schematically dominant
maps; the tensor square remains schematically dominant because all schemes over
the field are flat. Restricting the operations along the closed immersion gives
the group law. The projection and inclusion are actual homomorphisms and their
composite is the given homomorphism.

The image is affine. If the original target is locally of finite type, so is the
image. Geometric reducedness descends from the source along the quasi-compact
schematically dominant projection. Hence a smooth source gives a smooth image
by Mathlib's smoothness theorem for geometrically reduced group schemes locally
of finite type over a field.

This module does not yet assert flatness or surjectivity of the projection.
