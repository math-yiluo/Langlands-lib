# The projective linear torus fixed-point dimension bound

`ProjectiveTorusFixedPointDimensionStatement.{u}` states Milne's
*Algebraic Groups* (2017), Proposition 20.11, printed pp. 410–411
(PDF pp. 426–427). It is a proposition definition, with no proof supplied.

The coefficient field `k : Type u` is algebraically closed, with arbitrary
characteristic. The commutative group scheme `T` is a split torus.
The nonempty reduced finite-type scheme `X` lies over `Spec k`; finite type
is expressed by `LocallyOfFiniteType X.hom` and `QuasiCompact X.hom`.
Neither irreducibility nor smoothness of `X` is assumed. Its action is an
actual `SchemeAction T.toGrp X`.

An integer `n : ℕ`, an actual representation
`ρ : MatrixRepresentation T.toGrp (Fin (n + 1))`, and a morphism
`φ : X ⟶ ProjectiveOrbit.ambient n (CommRingCat.of k)` are supplied.
Here `MatrixRepresentation` is a homomorphism to the actual general linear group
scheme, with a chosen coordinate basis. The target of `φ` is the actual relative
projective space over `Spec k`, and the underlying morphism of `φ` must be a
closed immersion.

`ProjectiveOrbit.IsMatrixEquivariant a ρ φ` says on every relative scheme test
that applying the action and then `φ` agrees with the projective action of the
matrix obtained by evaluating `ρ`. Thus the hypotheses describe a closed
subvariety of the projectivization of a finite-dimensional torus representation,
stable under that representation's action, as in Proposition 20.11.
Properness follows from this projective closed embedding; it is not a substitute
for the representation and equivariance hypotheses.

Dimension means Mathlib's `topologicalKrullDim X.left`, valued in
`WithBot ℕ∞`. For every natural number `d` below that dimension, the conclusion
gives an injective family indexed by `Fin (d + 1)` of actual rational sections
`Spec k ⟶ X` over `Spec k`. Each section satisfies `SchemeAction.IsFixed`,
which quantifies over every relative test scheme and every torus point on it.
It asserts scheme-theoretic fixedness, including after nonreduced tests,
rather than only invariance under `T(k)`.

This finite-family formulation means there are at least dimension plus one
distinct fixed rational points whenever the dimension is finite; it also
expresses the correct arbitrarily large finite lower bounds if dimension is
infinite. It remains meaningful when the fixed-point set is infinite, without
interpreting its cardinality through `Nat.card`.

Over an algebraically closed field all tori split, so the split-torus hypothesis
gives the source's full algebraically closed torus scope. Milne reduces to that
scope and, since a torus is smooth, rational invariance of a rational point
agrees with the all-test fixedness used here. The source treats irreducible
components in the proof; the stated proposition allows reducible `X`.
Its eigenvector-basis and hyperplane induction is not implemented in this file.

The registered official errata snapshot of 2026-11-02 was read in full.
Its Chapter 20 corrections concern pp. 417, 419 and 420, and do not alter
Proposition 20.11. This statement supplies a geometric prerequisite for
homogeneous-quotient dimension arguments; it proves no fixed-point lower bound
or rank-one positive-root theorem.
