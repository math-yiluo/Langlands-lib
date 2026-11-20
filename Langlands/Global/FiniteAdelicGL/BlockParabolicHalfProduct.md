# Finite-place product of the adelic parabolic half character

`parabolicHalfCharacter_ofFinite_eq_prod` applies the actual adelic positive parabolic half character to a finite adelic parabolic matrix inserted with infinite component one. For any finite set containing its nonintegral local coordinates, the result is the product of the canonical local positive half moduli over that set.

The proof inducts on the finite set. With an empty set the finite matrix and its inverse are integral everywhere. Its adelic insertion is in the standard compact parabolic intersection, where the half character is one. At an inserted place, remove the identity-supported factor of the matrix at that place. The residual matrix has identity coordinate there and the original coordinates elsewhere. Multiplicativity reduces the assertion to the single-place normalization equality and the induction hypothesis.

This identity follows from the published determinant character and the actual finite local inclusions. Getz and Hahn (2024), §8.1, p. 213 (PDF 226), specify the positive normalized local covariance. Section 10.1, p. 271 (PDF 283), describes the place factorization of normalized adelic induction.
