# The integral split torus clause for a supplied descended model

`unramifiedTorusClause` proves the exact published proposition
`UnramifiedTorusClauseStatement.{u}` at arbitrary universe `u`.

The implemented proof first puts the character-valuation kernel of the
unramified split torus into the zero subgroup of the supplied datum, using
`UnramifiedZeroDatum.map_split_characterValuationKernel_le_zeroPoints`.
Normality of that zero subgroup and the supplied apartment fixedness put the
conjugated kernel in the intersection in the model's given point equality.
This argument does not require independence of the datum.

The published bounded-point extension theorem then constructs an actual closed
split torus of the neutral model, with generic isomorphism to the original
torus and the required conjugated generic commuting square. Its hypotheses use
the algebraically closed residue field of the unramified integers, the
equivalence of normalized and spectral valuations, and the exact intersection
of those integers with the base field.

Finally the generic inclusion is maximal split by transport along the generic
and inner isomorphisms. Henselian specialization of split rank, applied to the
smooth affine neutral model, makes the actual special-fibre inclusion maximal
split. This uses `isMaximalSplitTorus_residue_of_generic`, with connected
reductivity only on the generic fibre. The resulting maps form the required
`IntegralTorusData` and satisfy both clauses. Nonemptiness and boundedness of
the supplied subset are not needed in this proof once its fixedness and the
model's point equality are assumed.

The proof is derived from the published Library inputs named above. The source
comparison and general scope are those of the unchanged statement pair; no
additional literature assertion or mathematical premise is introduced.
