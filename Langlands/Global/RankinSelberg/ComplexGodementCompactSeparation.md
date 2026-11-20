# Separation at identity by compact Godement sections

Fix a right-invariant Haar measure on the smaller complex general linear group. Take a compact-finite vector in the larger upper Borel standard module with nonzero value at the identity. The proposition supplies a compactly supported smooth invariant cutoff for the cofactor lift and a compact-finite vector of the retained smaller standard module. The resulting Godement section has strictly positive real value at the identity.

The positive compact pairing theorem chooses the smaller vector. Lean first uses a cutoff equal to one on the unitary trailing rows. On that locus the cofactor lift contributes the inverse distinguished determinant character, which cancels the character in the integrand. The compact average of the preliminary integrand therefore has positive real part at the identity. It has the same value on the entire smaller unitary group and is continuous.

Lean then takes a second cutoff whose support forces the smaller variable into the open set where that real part is positive. The final cutoff is the product of the two cutoffs. It still equals one on the unitary trailing rows and is supported where the cofactor completion is invertible. Invariance of the second cutoff factors it out of the compact average. Fubini and right invariance of Haar measure identify the integral of that average with the original integral. The real part is continuous, compactly supported, nonnegative everywhere and positive at the identity, so its integral is positive.

This is the separation step of a compact-finite spanning proof for Jacquet's Godement sections.

Hervé Jacquet, *Archimedean Rankin–Selberg Integrals* (2009), §7.1, Proposition 7.1(v), pp. 44–46.
