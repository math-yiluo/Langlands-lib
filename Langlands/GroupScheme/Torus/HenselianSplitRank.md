# Split rank under Henselian specialization

This internal derived helper lifts the existence of a closed standard split torus
in a quotient-field fibre of a smooth affine group over a Henselian local ring.
It preserves the finite indexing type and hence the rank. It does not assert
that the chosen lift reduces to the original inclusion.

The proof uses the published smooth representation of the actual Hom presheaf
from a split torus, restricts to the open locus of closed immersions through the
given point, and lifts that point to a section by the published Henselian smooth
section theorem. Pulling the universal homomorphism back along the section gives
the required closed immersion. This is a derived result from those Library
proofs, with no additional literature claim.

`henselianClosedSplitTorusLift` chooses such an inclusion together with its
closedness proof. `splitRank_residue_le` applies this lifting to every finite
standard split subtorus and compares the suprema defining split rank. The target
field fibre may be any field with an algebra structure over the ring.

`IsSplitSubtorus.isMaximal_of_card_eq_splitRank` proves maximality by expressing
a factorization through another split torus in standard coordinates. Its
monomorphism gives one rank inequality, and the ambient split rank gives the
other. The published equal-rank monomorphism theorem makes it an isomorphism.

Finally, `isMaximalSplitTorus_residue_of_generic` concerns a closed split torus
in a smooth affine group over a Henselian local ring. It assumes the chosen field
fibre is connected reductive and that the torus there is maximal split. The
published rank part of maximal split torus conjugacy identifies its rank with the
generic ambient rank. The rank inequality above and the closed residue torus
force equality on the residue fibre, giving maximality there. No reductivity or
connectedness of the residue fibre is assumed. The field fibre is called generic
in the theorem name, but no fraction-field hypothesis is needed by its proof.
