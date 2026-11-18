# Restricting the weak standard integral to an intermediate Levi

This derived comparison works for a locally compact nonarchimedean group and
an intermediate Levi carrying those same properties. It uses the supplied
semidirect decompositions and the split radical-quotient comparison.
The quotient measurable spaces are the canonical Borel spaces. The
coefficient object inside the Levi is the pullback along the continuous
isomorphism from the literal inducing subgroup in that Levi to the original
inducing subgroup. The representation-carrier and group universes are
independent.

`NestedRestrictionFormula` is the normalized stages evaluation identity at
one ambient point `g`. At an intermediate Levi point `l`, the restricted
function evaluates as the original function at `l g`, multiplied by the
inverse of the supplied character at `l`. For a character trivial on the
inner target radical, the representative formulas for the two quotient
charts give the same scalar multiple for the two integrands. The weak
integral uses the exact pushed-forward measure `nestedQuotientMeasure`.
Smooth dual tests are preserved by the continuous equivalence of the two
inducing groups. Transport of the scalar integrals and complex homogeneity
then give the representing vector in the original coefficient carrier.

`nested_domain_eq_top` applies the same formula to a supplied surjective
linear restriction at `g = 1`. Every inner source vector has an ambient lift.
If every ambient source vector admits the original weak integral, that lift
supplies the inner representing vector at every inner evaluation point.
These are the weak-integral and domain comparisons needed for the stages
identity in Waldspurger 2003, IV.1(14), printed p. 284.
