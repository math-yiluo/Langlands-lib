# Scalar action at a positive upper bound

`Langlands.Henniart.Numerical.HasUpperScalarAction K A a` is an internal predicate for the count proof. It says that the restriction of the actual Weil representation `A` to the actual upper ramification subgroup at `a` is scalar, with an algebraic character of that subgroup into `ℂˣ` giving the scalars.

`hasUpperScalarAction_of_trivialAbove` proves the predicate for a continuous representation of rank `p^i` that is irreducible on inertia and trivial on every upper group at a real index strictly larger than `a > 0`. The field and representation-carrier universes are independent. `hasUpperScalarAction_of_torsionOne` gives the version for a representative of an irreducible Weil class of torsion number one and last break at most `a`, using the inertia criterion and the last-break comparison.

## Implemented proof

Choose a finite inertia presentation by continuity. The presented action pulls back along the surjective inertia restriction to the original inertia action, so the finite inertia action is irreducible. It stays irreducible on the first lower group: the restriction is semisimple by Maschke's theorem, and the quotient is cyclic of order prime to the residue characteristic, hence of order coprime to the rank. The cyclic restriction criterion applies.

The image of an element of the actual upper group at `a` lies in the finite upper group at `a`. Its commutator with any element of the first lower group is in a finite upper group at some index `b > a`, by the mixed-depth bound. Comparison of actual and finite upper fixed spaces gives triviality of the finite action there. Thus each of the indicated upper elements commutes in the representation with the irreducible first-lower-group action. Schur's lemma gives an invertible scalar. Evaluating on one nonzero vector picks out these scalars and gives a homomorphism by the eigenline character construction.

## Provenance and scope

This is the scalar-action step of Guy Henniart, *La conjecture de Langlands locale numérique pour GL(n)*, Ann. Sci. École Norm. Sup. (4) 21 (1988), Proposition 3.3, pp. 508–509 (registered source `henniart-1988-numerical`). The implementation works with finite inertia presentations and does not require an absolute wild inertia construction. It does not yet descend the scalar character to a graded unit character of the base field, construct the twisting equivalences, or prove the conductor-count equality.
