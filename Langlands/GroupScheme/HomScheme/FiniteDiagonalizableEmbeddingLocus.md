# The quasi-compact embedding locus for finite diagonalizable sources

Let `i : D_R(M) → G` be a homomorphism from the standard diagonal Hopf spectrum
for a finite abelian group `M` into an affine group scheme over `Spec R`.
`embeddingOpen i` is an actual open subscheme of `Spec R`. For every scheme
`T` and every map `b : T → Spec R`, the map `b` factors through this open
exactly when the base change of `i` is a closed immersion. Thus the
restriction of `i` to this open is itself a closed immersion. If the affine
ambient group is locally of finite presentation, this open is quasi-affine.
No Noetherian, reducedness, characteristic or flatness hypothesis is imposed.

This is derived infrastructure. The complement of the open is the zero locus
of the finite product of the degree coefficient ideals of the actual Hopf
coordinate map. The scalar-extension criterion in `FiniteDiagonalCoalgebraLocus`
and the published tensor-coordinate comparison identify membership for all
affine spectrum tests with closed immersion. Closed immersion is local on an
open cover of the base, so the criterion extends to every test scheme. The
actual open-immersion lift gives the stated factorization property.

Finite presentation of `G` gives finite-type coordinates. The coefficient-ideal
lemma proves finite generation of the complementary ideal; the associated
open in a prime spectrum is consequently compact. Its immersion into the
affine base then gives quasi-affineness. This module constructs the embedding
locus for a supplied family; choosing the Hom family and its automorphism
action is a separate step.
