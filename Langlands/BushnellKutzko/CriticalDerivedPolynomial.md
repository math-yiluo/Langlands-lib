# The monic lift of the normalized residual polynomial

Internal implementation of the choice of a polynomial for the degree-zero normalized element, as in the cyclic construction of Bushnell–Kutzko (1993), §2.5, for use in (2.4.1)(iii).

Suppose the restriction of the normalized endomorphism has the same degree-zero symbol as an integral scalar in the original field, and each integral coefficient over the new base has a scalar match inducing a specified residue map. Evaluating an integral polynomial in the endomorphism matches evaluating it in those scalar representatives, term by term. Taking residues of that scalar sum gives the evaluation of the polynomial reduced via the residue map.

Take the minimal polynomial of the matching scalar's residue over the image of the new base residue field, using the finite residue field of the original extension for integrality. Its monic lift has unit constant coefficient when the matching residue is nonzero. Its reduction is irreducible, and evaluating it at the endomorphism lies in depth one, by the scalar residue test and the comparison of the lattice sets. Neither the choice of the individual coefficient matches nor the proof requires a characteristic-zero lift of the residue-field homomorphism.
