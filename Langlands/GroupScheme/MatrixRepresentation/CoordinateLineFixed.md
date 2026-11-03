# Fixed coordinate vectors from commutators and unipotent factors

This internal module connects the character of an actual stabilized coordinate
line to pointwise fixedness of its chosen coordinate vector. It is derived
from the existing character, rational-point lifting, rational-point density,
unipotence and matrix-representation interfaces.

The function `rationalPointProductMap a t` sends a pair of base points of `U`
and `H` to the product of their images in `B`. Surjectivity of this function
means that every point of `B(k)` has such a factorization. It imposes no
surjectivity requirement on points over arbitrary test schemes.

For a reduced group locally of finite type over an algebraically closed field,
a character is zero if its values on base points are one. The proof compares
the underlying morphisms to the separated multiplicative group using
`hom_ext_rationalPoints`. This obtains equality of actual scheme morphisms,
and therefore equality of the characters on every scheme test.

Suppose `i : H ⟶ N`, `φ : H ⟶ H` is scheme-surjective and locally of finite
type, and `x ∈ N(k)`. If `i(φ(s)) = x i(s) x⁻¹ i(s)⁻¹` on base points,
every character of `N` restricts to zero on `H`, provided `H` is reduced
and locally of finite type. Each base point lifts through `φ`; a character
kills the resulting commutator; the preceding density argument concludes.
Surjectivity on points of arbitrary test schemes is not assumed.

A second character criterion assumes that `rationalPointProductMap a t` is
surjective, so that every point of `B(k)` is a product
of a point from a specified unipotent group `U` and a point from a specified
group `H`. A character trivial on `H` is also trivial on `U` by the
representation-theoretic definition of unipotence. It is consequently one
on `B(k)`, and reduced finite-type density again makes the character zero.
This lemma does not construct that factorization or require normality or
uniqueness of either factor.

Over any commutative base ring, the coordinate-line action equation proves
that a subgroup on which the actual coordinate-line character is zero fixes
the chosen coordinate vector on every scheme test. The final theorem combines
this observation with the two algebraically closed field criteria above.
Its character belongs to the actual line-stabilizing group `N`; the
representation is not presumed to extend a one-dimensional action to a
larger group.

The module retains the commutator identity and rational factorization as
explicit hypotheses. It supplies no solvable-group decomposition, Borel
normalizer theorem, or claim of Borel normalizer completion.

The line character used here is the additive rational character
`coordinateLineRationalCharacter` from `CoordinateLineCharacter`.
