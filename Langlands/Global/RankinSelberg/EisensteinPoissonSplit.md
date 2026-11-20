# Poisson decomposition of the unfolded Eisenstein series

This module implements the pointwise Poisson argument from Cogdell (2004), §2.3,
printed p.209. The Poisson identity for a pair of theta kernels includes the two
zero-vector values. Applying the identity at the transpose inverse gives the
identity with the kernels reversed.

The proof splits the unfolded integral at determinant norm one on the scalar
fibre. Inversion of the idele and transpose inverse of the group point negate
the height. They also exchange the character and spectral parameter with their
duals. The change of idele variable preserves the normalized Haar measure.
The inverse image of the rational-idele fundamental domain is another fundamental
domain, and the strict positive cut of the Mellin kernel is invariant under
principal ideles. The zero-height set is null by the log-norm pushforward.

The negative part therefore becomes the positive part for the dual parameters,
plus the two constant terms from Poisson summation.
