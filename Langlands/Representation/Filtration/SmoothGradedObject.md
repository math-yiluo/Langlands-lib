# Actual smooth graded objects

`Langlands.SmoothRep.IrreducibleGrothendieckProof.gradedSmooth` equips each
actual graded representation of an object filtration with inherited
smoothness, using subrepresentation smoothness and surjective transfer
along the actual quotient projection. The coefficient field, group and
representation carrier have independent universes `uR`, `uG` and `uV`.
The group has an arbitrary topological space structure, and the carrier
universe is unchanged.

This is the existing construction extracted unchanged from
[`Smooth/IrreducibleCompositionFactors`](../Smooth/IrreducibleCompositionFactors.md).
Its original declaration name and type are retained. The lower placement
allows finite-filtration extraction and composition-factor sums to reuse
one construction without importing Grothendieck-group infrastructure into
the extraction argument. `ObjectRepFiltration.smoothGradedObject` in
[`ActualGradedExtraction`](ActualGradedExtraction.md) is an abbreviation
for this declaration. The underlying representation is the actual upper
step modulo the lower step, with its existing quotient action.

The construction imports only `Filtration.ObjectDefinitions` and
`Category.Subquotients`. It asserts no new mathematical result and uses
no classification theorem.
