# Normalizing points of tori in connected solvable groups

This module supplies an internal helper for the stabilizer assertion in
`WeylBorelSimplyTransitiveStatement`. Over an algebraically closed field, every
base point of a smooth connected solvable affine group that normalizes a closed
torus centralizes it. The second theorem specializes this result to a maximal
torus. Both theorems are uniform in the universe.

The source motivation is Milne, *Algebraic Groups* (2017), Proposition 17.53,
printed page 369, registered as `milne-2017-algebraic-groups`. Its stabilizer
argument uses the trivial intersection of a torus with the unipotent part of a
Borel subgroup. The helper here abstracts that argument to a closed torus in a
smooth connected solvable affine group. The retained official errata dated
2026-11-02 contain no correction to Proposition 17.53.

The implemented proof uses the published theorem `solvableTorusQuotient` to
obtain a split torus quotient `q : H ⟶ D` whose full scheme-theoretic kernel
equals the range of a closed unipotent subgroup. The published theorem
`IsUnipotent.mono_torus_quotient`, instantiated with
`unipotentClosedSubgroup`, makes the composite `f ≫ q` monic. Thus the proof
uses trivial intersection on all scheme tests, including nonreduced tests.

If the point normalizes `f` through an automorphism of the torus, compose the
normalizing equation with `q`. The published theorem
`innerIso_hom_comp_of_isSplitTorus` makes conjugation invisible in this
commutative quotient. Cancellation of the monomorphism `f ≫ q` shows that
the induced group homomorphism of the torus is the identity. Substitution into
the original normalizing equation proves centralizer membership.

No quotient section or maximality argument is needed. The maximal-torus
specialization uses only the torus and closed-embedding components of
`IsMaximalTorus`.
