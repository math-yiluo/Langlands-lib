# Fixed-character model-star covariance

This internal helper keeps the full plus Fourier transform on the Schwartz
factor of the original actual coefficient tensor space. It does not transport
the coefficient character or replace the action by a different Fourier action.

Here `F` is a canonical p-adic field for a prime `p`, with its canonical topology
and Borel measurable structure. The supplied `ψ` is a continuous nontrivial
unitary additive character, and `ν` is the supplied additive Haar measure.
The full Fourier map and its covariance use the supplied certificate
`hself : IsSelfDual ψ ν`; self-duality is a separate premise from being Haar.

The intrinsic additive Haar character is identified with the residue-normalized
absolute value using the published p-adic scalar Haar scaling theorem, evaluated
on the compact open integer ring. This preliminary comparison needs only an
additive Haar measure and does not use self-duality. The full Fourier covariance of `rectangularRho0`
then proves covariance on pure tensors, and tensor induction extends it to every
algebraic test tensor. At an inverse-transpose group element, the scalar is
`|det k|^(r+1)`. This is derived from the published scalar and Fourier results;
it is not an additional hypothesis on the model integral.

This helper is valid for every algebraic representation and standard-character
functional, including zero, in independent field and module universes. It imposes
no smoothness or irreducibility hypothesis, and includes `r = 0`. It proves only
the stated covariance; the model integral equality is a separate obligation.

The inverse-transpose determinant calculation reuses the published
`RankOneGammaTwist.determinant_inverseTranspose`.
