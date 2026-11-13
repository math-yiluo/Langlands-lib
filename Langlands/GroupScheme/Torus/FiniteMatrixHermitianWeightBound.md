# Hermitian weight bound for a faithful finite matrix algebra torus

This internal derived lemma applies to an actual split-torus morphism into the
finite matrix algebra unit group. It assumes that the morphism is a monomorphism
on schemes and that its inverse universal Laurent matrix preserves the full
supplied nonsingular Hermitian Gram matrix. Establishing that isometry equation
from a particular all-test presentation is a separate obligation. The fields and
specified field involution have no characteristic or infinitude restriction.

The proof takes the basis of coefficient-projector columns from
`exists_weightBasis`. Its weights generate the full integral character lattice,
and each basis column is a Laurent eigenvector. Pairing preservation forces the
full Hermitian pairing of columns to vanish unless their weights sum to zero.
`HermitianWeights.exists_isotropic_of_weightBasis` then selects a subfamily with
no opposite pair, spans an actual totally isotropic L-submodule and bounds its
dimension below by the torus dimension. `weightIsotropicSubmodule` selects the actual submodule just constructed.
The actual attained Witt index bounds
this submodule's dimension above. The linear-first convention is the flipped
full Gram pairing, so the eigenvector orthogonality is used with the two indices
exchanged. No assertion about the full group's split rank is made in this lemma.
