# Pointed torus domination from diagonalizable parametrizations

This is an internal construction toward rational conjugacy of maximal tori. It
combines the implemented free/finite diagonalizable decomposition, residue-field
separability, and dominant scalar-extended residue-fiber construction.

For an arbitrary base scheme, `PointedTorusDomination.pointedNormalization x p`
is the actual morphism obtained by composing `p : X → H` with left translation
by the inverse of `p(x)`. The specified source section maps to the identity, and
normalization preserves dominance because translation is a scheme isomorphism.

Over any field `k`, let `Λ` be a finitely generated abelian group and let `H` be
an affine geometrically integral group scheme. A dominant scheme morphism
`D(Λ) → H` gives pointed split-torus domination of `H_L` for some finite separable
extension `L/k`. No multiplicativity or pointedness is required of the initial
morphism.

The proof decomposes `D(Λ)` into a split torus times the full finite
diagonalizable group `D(A)`. The dominant residue-fiber theorem selects a prime
`P` of `k[A]` whose actual fiber map to `H_κ(P)` is dominant. The field `κ(P)` is
finite and separable over `k`; the scalar extension of the split torus remains
split. Translating the target by the inverse of the image of its source identity
makes this dominant map pointed. The proof does not select the identity
component of the diagonalizable source and does not discard nilpotents of the
finite factor.

All characteristics and imperfect fields are retained. This unit constructs a
parametrization after a finite separable extension; splitness of a unipotent
target, descent, and the full conjugacy theorem remain separate obligations.
