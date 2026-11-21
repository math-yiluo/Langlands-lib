# Morphisms of actual p-divisible groups

`PDivisibleGroup.Hom` acts by a group scheme homomorphism on every finite
level and commutes with inclusions and transfers. The inclusion diagram
functor is fully faithful. In particular `Hom.ofNaturalTransformation`
recovers the tower morphism from the maps that commute with the inclusions.

To see why the transfers commute, compose both possible maps with the
corresponding inclusion of the target system. The scalar factorization
makes both composites the same multiple of the original map at the
larger level. The exact sequence makes the target inclusion injective on
points of every affine test. The source level is finite over the affine
base, so its own affine test detects equality of the original maps.

Composition and addition are given by the actual group scheme maps at
each level. This gives a preadditive category with a fully faithful additive
inclusion diagram functor. The morphisms and iterated transitions are those
of Tate, *p-Divisible Groups* (1967), §2.1, printed p. 161 (PDF p. 2), in the
paragraph defining homomorphisms and the sequence (2).
