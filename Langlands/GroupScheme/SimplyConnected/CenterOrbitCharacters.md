# Full star orbits and actual centre characters

This is an internal construction over every field and in every characteristic.
The input is actual `TitsIndexData d` for an affine, locally finite type
semisimple group scheme. The full geometric centre and its actual characters
are the constructions imported from `TypeD4CenterCharacters`.

`starOrbitVertices a` is the finite set of simple vertices reached from `a`
by the full absolute Galois star action. It includes each vertex once,
regardless of how many Galois elements reach it. Its membership theorem
states the defining existential equality. The action laws show that every
absolute Galois element permutes this finite set.

For a simply connected group, `centerOrbitCharacter hsc a` sums the actual
fundamental characters restricted to the full geometric centre over that
finite orbit. `centerOrbitCharacter_galois` proves that this sum is fixed
by every ordinary absolute Galois automorphism on that actual character
group. The proof applies the imported equivariance of individual fundamental
centre characters and reindexes the finite sum by the star permutation.

`centerFundamentalCharacter_fixedBy_vertexField` proves that the individual
fundamental character is fixed by every automorphism of the original
separable closure fixing the actual vertex field pointwise. It combines the
published fixed-field/stabilizer equality with the same centre-character
equivariance. This assertion is invariance in the original character group;
it does not construct a character over the vertex field.

A globally fixed vertex has singleton orbit, and its orbit character is its
original fundamental character. In type D4, a complete numbering of every
Cartan entry by the actual `CartanMatrix.D 4` fixes the centre at vertex 1
and the leaves at 0, 2 and 3. If no leaf is globally fixed, the published
star-transitivity theorem shows that each leaf orbit is exactly these three
leaves. The proof also checks that a leaf cannot map to the centre, using
the fixed centre and injectivity of the star permutation.

Consequently `centerOrbitCharacter_D4_eq_zero_of_no_fixed_leaf` identifies
the orbit character with the sum of the three actual leaf characters and
applies their imported zero-sum relation. These conclusions have no rank-one,
local-field, perfection or characteristic hypothesis.

This is a finite-orbit and actual-character prerequisite. It constructs no
Brauer obstruction, Tits algebra, descent to a vertex field, corestriction
map, anisotropic-kernel comparison or local D4 exclusion. In particular,
the zero orbit character alone does not prove the local enumeration.
