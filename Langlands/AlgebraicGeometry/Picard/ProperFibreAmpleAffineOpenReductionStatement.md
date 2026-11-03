# Reduction of the proper-family affine-neighbourhood statement

`ProperFibreAmpleAffineOpenReductionStatement` is the implication
from `ProperFibreAmpleSpreadingStatement` to
`ProperFibreAmpleAffineOpenStatement`, in the same arbitrary universe.
It is an internal derived statement that isolates the application step
of the proper-family proof.

The premise is the entire published spreading proposition: for every
proper morphism to a locally noetherian base and every specified line
bundle ample on one residue-field fibre, that bundle is ample on the
inverse image of some affine open neighbourhood of the base point.
The conclusion is the entire published finite-set proposition: every
finite set of points above that point lies in a single affine open
of the total space.

The intended reduction applies the generic theorem that a finite set
on a scheme carrying an ample line bundle has an affine neighbourhood,
then maps that neighbourhood into the original total space under the
open immersion. Both imported propositions retain their original
hypotheses and quantifiers, including arbitrary base points, nilpotents
and the empty finite set. This statement supplies no proof of the
spreading premise or of the unconditional conclusion.

This is a formal interface for a derived argument between the two
named Library propositions, with no additional external source claim.
