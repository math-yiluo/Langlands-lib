# Character lines and unipotent characters

This internal module associates an actual one-dimensional matrix representation
with a rational character by composing it with the published scalar torus in
`GL_1`. Its point matrix on every scheme test is the scalar matrix of the
character value.

The representation definition of `IsUnipotent` supplies a nonzero fixed vector
for that character line. Its unique coordinate is nonzero in the base field,
so its image in the global sections of every scheme test is a unit. The
fixed-vector equation then cancels this unit and proves that every character
value is one. Character extensionality proves that the character itself is zero.
This proof needs no algebraic closedness, smoothness or finite-type hypothesis.

The general lemmas `characterEval_commutator` and
`characterRestrict_injective_of_scheme_epi` record that characters kill pointwise commutators and that
restriction along a group homomorphism whose underlying scheme morphism is
epimorphic is injective. The first uses the commutativity of global units, and
the second cancels that scheme epimorphism on the underlying morphisms.

All content is derived directly from the existing representation, unipotence,
character and group-scheme definitions. It is intended as a prerequisite for
the stabilized-line argument in the Borel normalizer proof and makes no Borel
normalizer claim.
