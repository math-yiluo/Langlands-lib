# Complex conjugation of real standard modules

These internal constructions use the Library's standard model for `GL_n(ℝ)`. `realBlockConjExponent` conjugates the exponent of each block. The sign or weight is retained because the real model reads the rank-two weight through its absolute value. The real diagonal characters are conjugated, and the positive real modulus factor of normalized induction is unchanged.

`realStandardConjugation` conjugates the values of a standard function. Smoothness is preserved. In the Fourier window of an induced block, conjugation changes the mode index from `j` to `−j`, so vanishing in the symmetric window is preserved. Compact finiteness follows from the conjugate-linear orbit span lemma. Pointwise conjugation is injective, commutes with right translation, and commutes with the right derivative for every real matrix direction.

The construction is derived from the actual principal series and Fourier conditions in `StandardModule` and reuses the Library's conjugation identities for the Fourier coefficients and right derivatives. It supplies the conjugation used with real standard-module contragredience in the Hermitian comparison.
