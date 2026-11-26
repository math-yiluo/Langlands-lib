# The ranges of compared infinite Whittaker models are the actual restrictions

`HasActualPlaceWhittakerRanges` states that each real or complex model map in `ModelData` has range exactly the set of corresponding restrictions of actual cuspidal Whittaker functions. The set of restrictions allows the finite offsets specified by `IsRealPlaceWhittaker` and `IsComplexPlaceWhittaker`.

The published comparison lifts all actual restrictions to the corresponding model range. For the other inclusion, choose the normalized reference tuple with nonzero global coefficient. At any place, freeze the other infinite factors and their group arguments at this tuple and at identity. Evaluating the comparison at the normalized slot gives the nonzero scalar of the resulting slice. Dividing the varying pure vector by that scalar realizes exactly its local model function as a single-place restriction, with finite offset one.

This is an internal derivation from the Library's normalized infinite Whittaker product. The comparison with the full Whittaker models of the specified archimedean standard modules is a separate input.

For every rank `n`, `finitePoint_one` identifies the image of the finite adelic identity with the identity of the full adelic group.
