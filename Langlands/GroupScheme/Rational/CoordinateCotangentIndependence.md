# Independence of actual cotangent character spaces

This internal module derives independence from the actual all-algebra eigenvector
definition in `CoordinateCotangent`. It does not assume a decomposition.

`exists_characterCoefficient` constructs, for each character `χ`, a linear
functional on the acting group's coordinate algebra that takes value `1` on
its character unit and `0` on every other character unit. The published result
`CharacterUnits.linearIndependent_unit` makes the character-unit linear
combination map injective. A linear left inverse followed by evaluation at `χ`
is the required functional.

`cotangentWeightSpace_iSupIndep` proves independence of the actual cotangent
character spaces. Apply the action at the universal point of the acting group
to a finite relation among cotangent eigenvectors. Their all-algebra eigenconditions
identify the result with the sum of the tensors of each character unit and
its eigenvector. The equivalence `cotangentTensorEquiv` identifies this with a
zero tensor relation. Applying the separating functional on the first factor
and the tensor left-unit equivalence extracts each eigenvector, proving it is
zero.

Both the target group and the acting group are affine over an arbitrary field.
The acting group need not be split. There is no finite-dimensionality or
characteristic restriction. This is a derived internal argument from the
published actual cotangent and character-unit constructions; it makes no
additional source claim.
