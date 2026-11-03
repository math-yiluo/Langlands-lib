# Whole-character pairing invariance of actual relative reflections

`rationalCocharacterEvaluation` extends evaluation of the actual character and
cocharacter lattice pairing to the full rational character space. Its value on
`toRat χ` is the rational image of the original integer pairing.

`IsRelativeReflection.rationalCocharacterEvaluation_invariant_of_span` starts
with a reflection on the actual relative-root span and a cocharacter orthogonal
to the reflection root. The reflection subtracts a scalar multiple of that root,
so evaluation is unchanged on the root span. The full actual Weyl action fixes
the range of rational-character restriction pointwise by
`relativeWeylFullRatAction_restrictionRange`. If the sum of those two subspaces
is the full character space, additivity proves evaluation invariance everywhere.

`IsRelativeReflection.latticePairing_schemeWeylCharacterAction` applies the
joint-spanning theorem
`IsConnectedReductive.relativeRootSpan_sup_restrictionRange_eq_top` for every
actual maximal split torus of a connected reductive group over any field.
Evaluation on `toRat χ`, followed by injectivity of the integer embedding in
the rationals, gives pairing invariance for every actual integral character.
No integral coroot or full-character reflection formula is assumed.

This internal derivation uses the joint-spanning construction by Worker 165 and
the existing actual full and restricted Weyl actions. It establishes a property
of every `IsRelativeReflection`; identifying any supplied Coxeter generators
with those reflections remains a separate obligation. It proves no
representation-theoretic expansion or final Aubert compatibility equation.
