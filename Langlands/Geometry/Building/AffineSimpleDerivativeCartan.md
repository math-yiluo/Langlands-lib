# Cartan extensions from deleted simple-gradient bases

This internal comparison identifies the integer Cartan matrix of a full
rational derivative base with the corresponding principal submatrix of the
actual affine chamber Cartan matrix. It retains the full derivative set.

Assume a deleted simple affine gradient family is independent and integrally
generates the full derivative lattice. If a supplied rational derivative base
has support exactly the image of that family, `deletedSimpleRootDerivativeEquiv`
identifies the family with the base's support. Injectivity uses independence
of the gradients; surjectivity uses the asserted exact support equality.

Root-coroot evaluations in the rational pairing are the original real
evaluations. Uniqueness of a coroot with prescribed derivative identifies each
simple derivative coroot with the coroot used in the affine chamber matrix.
Injectivity of the integer scalar map therefore gives equality of the integer
pairings, and hence of the two Cartan matrices on the undeleted nodes.

For a regular chamber with vertex-transitive Cartan matrix, any supplied
Cartan-preserving identification of a finite matrix `M` with this base gives
an extension of `M` on `Option I`. The new node is the deleted affine root.
Reindexing the actual chamber matrix transports its diagonal entries,
nonpositive off-diagonal entries, symmetric zero pattern, positive integer
left-kernel marks and vertex-transitive matrix automorphisms.

These are internal consequences of the imported constructions and finite
reindexing. Existence of the base, the geometric premises and an identification
of this base with an actual absolute group root datum remain explicit inputs.
This unit supplies no actual-group or splitting theorem.
