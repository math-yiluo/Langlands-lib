# Perfectness of semisimple groups by integral Weyl averaging

This proof establishes the unchanged published proposition
`Langlands.GroupScheme.SemisimplePerfectStatement.{u}`. For every field `k`
and every semisimple group scheme `G` over `k`, the full subgroup functor
`derivedSubgroup G` is top. The universe is arbitrary; the theorem includes
imperfect fields and positive characteristic.

The main step proves the published auxiliary assertion
`AlgebraicallyClosedSemisimpleMaximalTorusDerivedStatement`: every maximal torus
in a semisimple group over an algebraically closed field lies in the full
scheme-theoretic derived subgroup.

The proof uses the finite actual relative Weyl quotient acting on the integral
cocharacter lattice. For each actual root, the published intrinsic construction
provides a normalizer in its generic annihilating cocharacter centralizer that
inverts the root. Mapping this point through the centralizer inclusion gives
an ambient normalizer with the same character action. The inverse torus
automorphism also negates the root, as follows by composing the direct inversion
equation with its inverse. These are actual group-scheme morphisms.

The integral sum of all Weyl translates of a cocharacter is invariant under
every Weyl element. Pairing invariance and the root-inverting normalizer show
that the pairing of this sum with each root is its own negative, hence zero
in the integers. The published semisimple cocharacter-annihilator theorem,
which uses the finite scheme-theoretic centre, implies that this sum is zero.

Fix any closed subgroup containing all commutators. Each difference between
a Weyl translate and the original cocharacter is the cocharacter composed
with the actual torus commutator endomorphism, so it lands in this subgroup
on all test schemes. Summing over the finite Weyl group gives the negative of
the group order times the cocharacter. The order is nonzero because the group
contains its identity. The published saturation lemma removes this nonzero
integer multiple using fpqc descent along multiplication on the multiplicative
group; this also covers integers divisible by the characteristic. Coordinate
cocharacters then give containment of the entire split torus on every test
scheme. Intersecting over the closed subgroups containing commutators proves
the asserted derived-subgroup containment.

Finally, `semisimplePerfect` applies the published
`semisimplePerfect_of_maximalTorusDerived_of_torusGeneration` assembly with
this maximal-torus containment theorem and the proved
`reductiveFiniteTorusGeneration`. Over an algebraically closed field, finite
torus generation promotes containment to perfectness. The same assembly uses
preservation of semisimplicity under algebraic closure and fpqc descent of
perfectness to obtain the original arbitrary-field statement. No rational-point
equality is substituted for the all-test subgroup-functor conclusion.

The provenance is internal composition of the published intrinsic normalizer,
normalizer transport, finite relative Weyl action, Weyl averaging,
semisimple annihilator, torus commutator and fpqc saturation results.
The proof constructs no integral coroots and requires no root-datum existence
or universal reflection-existence premise. All structural inputs are supplied
by imported proved Library results, including the generation and descent
assembly; none remains a premise of `semisimplePerfect`.
