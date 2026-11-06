# The closed subgroup fixed by an endomorphism

Author: Worker 1368.

This is an internal construction from the Library's group-scheme points,
subgroup functors and representability-transfer interface, together with
Mathlib's scheme equalizers. It does not assert an external structure theorem.

For a group scheme `G` over any scheme `B : Scheme.{u}` and an endomorphism
`f : G ⟶ G`, `endomorphismFixedSubgroup f` consists, on every test scheme
`T` over `B`, of the points `g` satisfying `g ≫ f.hom.hom = g`.
Postcomposition with a group homomorphism preserves identity, products and
inverses, so these sets form subgroups; associativity proves restriction
stability. The tests include arbitrary nonaffine and nonreduced schemes.

The subgroup is the functor represented by the equalizer of the underlying
endomorphism and the identity. The proof of the factorization criterion uses
the equalizer lift and its defining equation. When `G` is separated over `B`,
this equalizer inclusion is a closed immersion, and the published
`SubgroupFunctor.isClosedRepresentable_of_scheme` transfers its group
structure and gives a closed representing group scheme. Smoothness or
connectedness of this fixed subgroup is not asserted.

A homomorphism `i : H ⟶ G` has its range in this subgroup precisely when
`i ≫ f = i`. The forward direction uses equality on all points; the reverse
direction composes the equality with each point. The same pointwise argument
proves that this subgroup is the full group exactly when `f` is the identity.

This supplies the closed fixed subgroup used in the planned proof of pinned
automorphism rigidity. It supplies no root-group fixedness, rank-one
factorization, or proof of that rigidity statement.
