# Actual identity comparisons of framed formal atlases

This internal module constructs the identity
`DrinfeldFramedAtlas.Comparison` of an actual framed representative.
It retains all local-field, central-division-algebra, embedded-subfield,
residue-field, fixed-frame and universe hypotheses of the existing
framed comparison interface. The coefficient base is one fixed actual
`Nilp` object, and its principal covers may be infinite.

Reflexive equality of residue maps gives the actual rational identity
on the extended fixed frame. Coefficient extension preserves this
identity on every test algebra. A diagonal actual target comparison
similarly gives the rational identity on each defined finer chart.

`ReducedFramingSquare.diagonal` compares the normalized actual framing
followed by the target identity with the frame identity followed by
that same framing. The proof uses the two identity equations just
described and the actual quasi-isogeny identity laws.
`ReducedFramingSquare.of_isDiagonal` applies the construction to any
specified reduced comparison which is identity on one refinement.

`FramingSquare.refl` uses the theorem that the actual quotient
reduction of the specified reflexive target comparison is diagonal.
It does not identify that reduction with the canonical reflexive
comparison of the reduced atlas: the actual resulting finer cover
and its identity formal coordinate map suffice.

`Comparison.refl` stores the reflexive actual target comparison,
reflexive residue equality and this proved framing square. Its
induced target point-functor map fixes every complete family.

The provenance is internal from the actual formal comparison,
quotient-extension and quasi-isogeny identity constructions, including
`SpecialAtlasComparisonIdentity`. No representing or universal object
is assumed. Transitivity, the framed quotient, varying-base
functoriality, group actions and representability remain separate.
