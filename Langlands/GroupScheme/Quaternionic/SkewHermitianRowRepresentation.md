# Representing skew values from an isotropic row

`SkewHermitianRowRepresentationStatement` takes an invertible skew Gram matrix over a ring with involution of the first kind and with `2` invertible in the ground ring. If an isotropic row has an invertible coordinate, the pairing represents every coefficient on which the involution acts by negation. The coefficient algebra may have zero divisors.

Using the inverse Gram matrix and the inverse of the chosen row coordinate gives a partner whose pairing with the isotropic row is one. The negative adjoint relation makes the reverse pairing negative one. Adding a suitable multiple of the isotropic row to the partner changes its self-pairing by twice that skew multiple. One half of the difference between the target and the partner value gives the desired representative.

This is a direct row calculation for the representation step following Lemma 5.2.3 in Springer's appendix to Kneser's *Lectures on Galois Cohomology of Classical Groups* (1969), printed p. 108 (PDF p. 114).
