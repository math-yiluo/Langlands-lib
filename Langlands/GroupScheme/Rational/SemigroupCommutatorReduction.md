# Reduction of the all-test semigroup bound to its geometric generators

This is internal proof infrastructure for the exact published
`SemigroupCommutatorStatement` in `WeightSemigroupStatement`. It does not prove
the geometric generator bound. The source motivation is CGP,
*Pseudo-reductive Groups*, second edition (2015), Proposition 3.3.5, printed
p.109 / PDF p.135, registered as
`conrad-gabber-prasad-2015-pseudo-reductive`. The group-closure argument here
is a derived implementation argument for the Library's actual definition.

`SemigroupGeneratorCommutatorBound b` requires the commutator bound only for
points in two individual smooth connected closed, action-stable subgroup
functors with the specified intrinsic Lie-weight support. It quantifies over
every pair of additive subsemigroups and every test scheme. The target is
still the constructed semigroup subgroup for the literal sum A+A'.

`commutator_closure_le_of_normalizes` is a group-theoretic lemma. If two
subgroup closures normalize K and all commutators between their generating
sets lie in K, all commutators between the two closures lie in K. Its proof
uses two subgroup-closure inductions and the product and inverse commutator
identities from Mathlib.

`subgroup_le_normalizer_closure_of_commutators` supplies the normalization
step for one subgroup and one generating set. It extends conjugation through
the generated subgroup by its universal property; applying the same argument
to an inverse gives both directions of normalizer membership. Keeping this
group calculation separate also bounds kernel-checking costs for the
scheme-valued application.

The absorption lemmas use closure under addition in each semigroup:
A+(A+A') is contained in A+A', and A'+(A+A') is contained in A+A'.
Neither argument inserts zero, assumes nonemptiness, or replaces positive
semigroups by submonoids.

`semigroupSubgroup_normalized_of_generatorBound` applies the generator bound
when A+B is contained in B. For a point of an A-generator it extends
conjugation across the B-closure using a subgroup comap. The inverse point
gives the other direction needed for normalizer membership. Subgroup closure
then extends normalizer membership across the A-closure.

`semigroupSubgroup_commutator_of_generatorBound` applies normalization to the
literal sum A+A' using the two absorption lemmas, then invokes the generic
closure lemma. `generatorCommutatorBound_iff` records that the generator input
and full pointwise conclusion are equivalent for a fixed actual action.
These reductions need no smoothness or splitness of the ambient group or
acting group. Those geometric hypotheses belong to the still-unproved source
bound on the admissible generators.
