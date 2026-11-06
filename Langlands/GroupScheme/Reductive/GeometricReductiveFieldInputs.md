# Original geometric-fibre inputs from field structure statements

This internal adapter applies three universal field statements to the actual
identity component of a specified original geometric fibre:
`RelativeRootReflectionExistenceStatement`, `RootReducednessStatement` and
`SplitRootLieLineStatement`. All three remain explicit inputs. The base ring
and universe are arbitrary, and the ambient smooth affine group's fibres may
be disconnected. An actual closed standard torus over the base, membership of
the specified point in the reductive identity-component locus, and
self-centralization of this torus in that geometric identity component are
also inputs. No initial torus is constructed and the universal openness
statement is not proved here.

The existing self-centralizing-locus theorem makes this actual torus a maximal
torus of the geometric identity component. Since it is a standard split
torus, it is also a maximal split torus. `geometricFieldReflectionData`
applies the universal forward reflection statement there and chooses its
actual reflection data. The statement also supplies centralization of each
full scheme-theoretic root kernel; the present consumer needs only its actual
reflection-data component. It does not replace these kernels by reduced or
smooth kernels.

`geometricExponentRoots_reduced_of_fieldStatement` applies field reducedness
to the two actual exponent characters. The field character-lattice coordinate
equivalence recovers equality or opposition of the original integer vectors.
The orientation is reversed to match the finite root-centralizer construction:
its second exponent equals the first or its negative.

`exponentWeightRank_eq_one_of_fieldStatement` applies the field root-line
statement to the actual root weight. Its supplied linear equivalence with the
original geometric field gives dimension one. The existing exact comparison
between geometric identity-component weight dimensions and relative exponent
ranks gives rank one for the original relative summand. The argument uses the
actual all-coefficient-algebra weight space throughout.

`identityComponentReductiveNeighbourhood_of_fieldStatements` passes these
constructed inputs to the integral-reflection neighbourhood constructor. Its
result is an actual open neighbourhood of the specified original point,
contained in the unchanged `identityComponentReductiveLocus`. The called
constructor derives root negation, constructs geometric reflection records
and every required centralizer good open, and performs finite ambient
assembly. No family of good opens is assumed here.

`identityComponentReductiveNeighbourhood_of_maximalFieldTorus` instead takes
maximality of the original geometric torus. It additionally takes the universal
`AlgClosedMaximalTorusCentralizerStatement`, applies it to this same actual
reductive geometric identity component, and obtains the self-centralization
used by the preceding constructor. The universal field statements and initial
closed torus remain hypotheses in both constructors; no pending proof or
publication is used as an established theorem.

The provenance is internal composition of the existing field statements,
maximality comparison, character coordinates, exact weight-rank comparison and
actual good-open construction. No new assertion from the literature is made.
