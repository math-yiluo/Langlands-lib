# Nonidentity normalizers from roots and solvable homogeneous quotients

This internal composition provides actual rational witnesses over algebraically
closed fields `k : Type u` of any characteristic. Its quotient constructions
retain `AlgClosedReductiveNormalSolvableTorusStatement` as an explicit input.
The ambient group is pseudo-reductive in the Library's sense.

`not_isCentral_of_relativeRoot` works over any field for an affine group locally
of finite type and a homomorphism `i : T → G` from a split torus. If an actual
relative root `χ` exists, `i` is noncentral. The proof applies
`root_restrict_eq_zero_of_isCentral` along the identity of `T`: centrality would
make `χ` zero, contradicting the definition of a relative root.

`Dynamic.nonfixedQuotientLiftOfRelativeRoot_of_structural` combines this fact
with `Dynamic.nonfixedQuotientLiftOfNoncentralSubgroup_of_structural`. For any
closed solvable `j : P → G` and flat, surjective, quasi-compact exact right-coset
quotient `q : G → Q`, it constructs a rational `g : Spec k → G` whose quotient
section is not fixed on all tests by `T`. Smoothness, affineness and connectedness
of the acting group follow from the supplied split-torus hypothesis. This
constructor requires neither properness nor separatedness of `Q`, nor maximality
of `T`, a factorization of `i` through `P`, or conjugacy of tori.

`nonidentityNormalizerOfNoncentralSolvableQuotient_of_structural` takes a
noncentral maximal torus `i`, a closed solvable `j : P → G`, an actual factor
`f : T → P` with `f ≫ j = i`, and `MaximalToriAreConjugate P`. It also takes a
smooth, surjective, quasi-compact exact right-coset quotient `q : G → Q` whose
target is proper. It first constructs the nonfixed rational lift by the
normal-closure argument, then passes it to
`nonidentityNormalizerOfNonfixedSmoothProperQuotient`. It returns an actual
rational normalizer point whose class in `N(k)/Z(k)` is not one. Geometry of the
maximal torus supplies the smooth connected affine source required by the
normal-closure construction.

`nonidentityNormalizerOfRootedSolvableQuotient_of_structural` takes instead a
split maximal torus with an actual relative root and applies the noncentral
constructor. These normalizer constructions require no supplied matrix
representation, line-stabilizer presentation, moving test point, nonfixed
section, whole-torus centralizer containment, or finiteness of the Weyl group.

The provenance is direct derivation and composition of the named Library
constructions, developed by Workers 1549 and 1547. The normal-solvable-torus
input, internal torus conjugacy, and actual smooth proper quotient remain
explicit. This file does not prove those structural statements, a dimension
bound for the quotient, or the unconditional positive-root uniqueness theorem.
