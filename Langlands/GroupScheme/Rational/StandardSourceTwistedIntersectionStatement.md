# Standard source intersections for minimum geometric terms

`StandardSourceTwistedIntersectionStatement` is an unproved internal structural
target for the actual geometric-term reduction in the rational-point Aubert
induction equation. It covers every field, connected reductive group, maximal
split torus and generic cocharacter, and every actual scheme-relative-Weyl
Coxeter system satisfying `IsRelativeWeylCoxeterRealization`.

For finite simple-root subsets `I,J`, a minimum representative `w` in
`W_I w W_J`, and every scheme-normalizer point `n` above `w`, put
`K = intersectionSubset cs I J w`. The property
`IsStandardSourceTwistedIntersection` states the two subgroup-functor equalities

`L_J ∩ Int(n)⁻¹(P_I) = L_J ∩ P_K`,

`L_J ∩ Int(n)⁻¹(U_I) = L_J ∩ U_K`.

All groups are the literal published standard subgroup functors at `rootSet`
of the finite labels. The preimage is `comap (G.innerIso n).hom`; at rational
points it is conjugation by `n⁻¹`. The equalities hold on every test scheme,
including nonreduced test schemes. The field universe `u` is arbitrary.
No assumption of splitness, quasi-splitness, perfectness, characteristic zero
or a reduced relative root system is added. Empty label types and empty or
full subsets are included.

These two equalities identify the source parabolic and radical of an actual
geometric term with the literal standard restrictions inside `L_J`.
The twisted Levi equality is a separate obligation: knowing the Levi alone
does not identify a parabolic or its radical. Together with that Levi equality,
these formulas supply the subgroup identities needed to compare the actual
source normalized Jacquet functor with the restricted standard Jacquet functor.
This file does not construct that functor comparison.

Two elementary adapters are proved. The first evaluates supplied all-test
equalities at the base scheme, using
`SubgroupFunctor.rationalPoints_comap_innerIso_hom_eq_map`.
The second applies this evaluation to every minimum representative and lift
covered by a supplied `IsStandardSourceTwistedIntersection`, then applies
`Subgroup.subgroupOf` and `Subgroup.inf_subgroupOf_left`. Its conclusions are
the exact parabolic and radical subgroup equalities inside the literal `L_J`.
Neither adapter proves the structural target.

The provenance is internal. The definitions in `StandardParabolic`, the actual
root-labelled Coxeter interface in `RelativeWeylCoxeterStatement`, and the
actual source intersections of `GeometricK0Target` specify the objects to be
identified. This target records the additional structural information needed
by that consumer, without claiming a proof from the interfaces. Transport to
the actual point-normalizer quotient still requires the separate normalizer,
centralizer and Coxeter-index comparisons. No topology, representation
preservation, normalized transitivity, Weyl conjugacy or geometric-lemma
identity is asserted here.
