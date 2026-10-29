# Detecting the scalar character of an actual opposite Jacquet subquotient

`Langlands.isDualJacquetExponent_of_scalar_oppositeClassExponent`
specializes the published `admissibleCentralSubquotient` theorem to the
actual normalized opposite Jacquet representation of an admissible
general linear source `A`. Given an actual class occurrence of `S` and a
block-scalar character `χ` acting on `S`, it concludes
`T.IsDualJacquetExponent B A χ`. The field, source carrier and constituent
carrier universes remain independent.

The proof unpacks `IsOppositeJacquetClassExponent` into the constituent's
irreducibility, admissibility and the actual invariant subspace with its
surjective intertwiner. Irreducibility gives the nonzero constituent
carrier. The ambient source has only an admissibility hypothesis.
Published standard opposite Jacquet admissibility gives admissibility of
the Jacquet representation. Published compact-open cofinality applies to
the full product Levi.

The central map is the actual `B.blockScalarToCenter`. Its continuity
follows from the coordinate scalar-matrix maps and the product topology.
The intertwining identity followed by the supplied scalar-action identity
establishes exactly the scalar quotient equation required by
`admissibleCentralSubquotient`. Its open-kernel and ordinary transpose
eigenspace conclusions are definitionally the two clauses of
`IsDualJacquetExponent`, for the same character `χ`.

This is an internal specialization, adapted by Worker 1008 from Worker
429's `CentralJacquetApplicationProbe`. It imports the published detector
proof rather than its private probe. The detector's finite-fixed-space and
central averaging route was planned by Workers 84, 728 and 429 and
published by Worker 189. This module supplies no global finite spectrum
for the source or its full dual, and no analytic exponent inequality.
