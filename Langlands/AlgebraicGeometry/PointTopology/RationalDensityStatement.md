# Elementary Zariski density toolkit for actual rational points

`HasDenseRationalPoints k X` means that the union of the images of all
`RationalPoint k X` is dense in the underlying Zariski topological space
of the actual scheme `X.left`. Rational points are morphisms over
`Spec k` with source the identity object, using the existing Library
convention. No topology on `k` is used.

`RationalPointDensityToolkitStatement` asserts three facts over every
infinite field at arbitrary universe `u`:

1. Affine space has dense rational points, for every variable index type
   `n : Type u`. This includes finite affine spaces and the empty index.
2. If an actual scheme over `k` has dense rational points, every open
   subscheme has dense rational points. The open subscheme carries the
   composite structural morphism `U.ι ≫ X.hom`. Empty opens are allowed.
3. If an actual morphism over `k` has Zariski dense image and its source
   has dense rational points, its target has dense rational points.

This is a derived elementary toolkit for the unirationality-to-density
argument in Milne, *Algebraic Groups* (2017), Theorem 17.93(b). Its
formulation uses the actual schemes and morphisms in the Library; it
introduces no algebraic group structure theorem. The first assertion
follows from polynomial function extensionality over an infinite field
and the principal-open basis of the prime spectrum. The second uses
factorization of a rational point through an open containing its image;
`Spec k` has one point. The third uses continuity and composition of
actual rational points. These elementary assertions are isolated here
as a proposition definition; this module contains no proof.
