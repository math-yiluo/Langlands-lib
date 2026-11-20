# Finite polynomial tests for ring-valued points

A ring-valued point of a locally finite type algebraic space over a field
comes from a finite polynomial test. The proof applies the filtered ring-point
comparison to the actual finite-subset-generated subalgebras of the coefficient
ring. Their inclusions form a colimit because every ring element belongs to a
stage and any two stages embed into the stage for their union. The Noetherian
field base turns the locally finite type atlas into a locally finitely presented
atlas, as required by the filtered ring-point comparison.

This is an internal consequence of the filtered ring-point comparison in
`SpaceFilteredRingPointProof.lean`. The finite-subset diagram follows
`ProperCoverFPApprox.lean`, using algebras over the given field as its objects.
