# Strict exponents and asymmetric actual associated Jacquet factors

This derived supporting unit composes the published strict-exponent tests for the
actual induction subspace and quotient with the coefficient-integral positive
form and the conditional unitary associated-support comparison. It retains the
exact strict-Jacquet square-integrability statement, the exact opposite Haar
reciprocity statement, and triviality of the ambient modular character. It does
not prove these inputs or the exact rank-one self-association proposition.

`strictJacquetPositiveForm` constructs a positive form on an admissible
irreducible smooth representation of the actual rational-point group with a
supplied full unitary central character and strict normalized Jacquet exponents.
It applies the retained square-integrability criterion for the Borel Haar measure
on the actual full central quotient. The proved compact-open cofinality supplies
a nonzero smooth-dual functional. The coefficient integral uses the derived
central-quotient right invariance from ambient unimodularity; no second
countability or quotient-unimodularity premise is added.

The two bound obstructions concern a supplied `InductionTwoJacquetFactors` datum
for the original standard index and its actual associated index, with supplied
scalar characters, whole-induction admissibility, a full unitary central
character on that induction, and vanishing of its standard Jacquet modules at
all proper outside indices. The original point-root comparisons,
standard-cocharacter and associated-subset laws, relative roots, rational-point
topology, radical closedness, and specified longest normalizer lift remain.
The first obstruction requires irreducibility of the inducing object; the second
requires nonzero associated Jacquet module of the whole induction.

For the subspace, admissibility is inherited along inclusion and the central
character is restricted. Strict bounds for the first scalar character give
strict exponents by `subspace_hasStrictNormalizedJacquetExponents`. Compact-limit
standard radicals and exclusion of noncentral negative tests at the full index
are derived from the original standard-cocharacter/root data. The actual
positive form then contradicts the nonzero original and zero associated Jacquet
pattern, using the exact opposite Haar premise and the proved opposite Iwahori
basis. The quotient argument uses the actual quotient map to inherit
admissibility and descend the central character, and applies the same argument
to the reverse asymmetry using the second scalar character.

These results do not construct the two-factor datum, outside-index vanishing,
the scalar characters or their conjugation relation, whole-induction
admissibility, or its full unitary central character. They do not eliminate the
unit-modulus branch or conclude self-association. Their provenance is entirely
internal composition of the named Library constructions.

The 1 local instance has module-specific names to prevent generated-name
collisions when related modules are imported together. The instance types,
bodies and local scope are unchanged.
