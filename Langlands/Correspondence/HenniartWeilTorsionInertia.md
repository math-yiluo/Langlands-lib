# Torsion number one and irreducibility on actual Weil inertia

`Langlands.Henniart.Numerical.WeilInertiallyIrreducible K σ` is the property
that a representative of the irreducible Weil class `σ` is irreducible on the
actual inertia subgroup. This predicate lets the inertia condition be used on
classes, in terms of the representations and restriction already defined in the
Library. It is an internal interface for Henniart's torsion-number-one strata;
it does not define or count the individual irreducible constituents on inertia.

The main theorem, `weilTorsionNumber_eq_one_iff_inertia_irreducible`, proves
that the published `Numerical.weilTorsionNumber K σ` is one exactly when the
restriction of **any** actual representative `A` of `σ` to `localInertia K` is
irreducible. The field and representation-carrier universes are independent.
The class predicate therefore agrees with the torsion-one condition.

## Implemented proof

1. The published geometric Frobenius lift has degree one; dividing a Weil
   element by the corresponding power of that lift leaves an element of the
   degree kernel, which is the actual inertia subgroup. This also identifies
   every algebraic character trivial on inertia with the published continuous
   unramified character of its value at that lift.
2. Continuity gives a finite inertia presentation with surjective restriction
   onto finite Galois inertia. Maschke gives semisimplicity there, and the
   surjective-pullback lemma of `CyclicRestriction` gives semisimplicity of the
   actual restriction.
3. On actual representatives, equality of an unramified twist class with the
   original class is equivalent to an intertwining equivalence with the
   actual twist. This uses injectivity of forgetting the property certificate
   and the quotient description of the isomorphism class.
4. If the stabilizer has natural cardinality one, the identity is its sole
   element, so there are no nontrivial self-twists by characters trivial on
   inertia. The cyclic-quotient restriction theorem applies with the
   geometric Frobenius lift and semisimplicity from step 2.
5. Conversely, an irreducible restriction forbids such a self-twist by Schur's
   lemma, as proved in `CyclicRestriction`. Evaluate its character at the lift
   to get that the stabilizing parameter is `1`, and conclude that the
   stabilizer has cardinality one.

Neither wild-inertia irreducibility nor the conductor-count step is asserted
in this module.
