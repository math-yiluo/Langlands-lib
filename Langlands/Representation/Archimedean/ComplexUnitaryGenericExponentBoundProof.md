# Exponent bound for unitary generic modules of GLₙ(ℂ)

`Langlands.Archimedean.complexUnitaryGenericExponentBound` proves
`ComplexUnitaryGenericExponentBoundStatement` at the published universe `uV`.
The inducing character of exponent \(t\) has radial part \(|z|^{2t}\), so
\(t\) is the exponent of the complex modulus \(|z|_{\mathbb C}=|z|^2\).

The injective standard parameter intertwiner realizes the irreducible module
on the compact-finite principal series and pulls back its invariant positive
form. After ordering by decreasing real parts, the compact duality pairing
gives an intertwiner into the series with Hermitian-dual characters, whose
real parts are increasing. The published opposite-order Hom result gives
equality of the two parameter multisets. The parameter list can therefore be
permuted into characters fixed by Hermitian duality and adjacent pairs of
equal angular weight with exponents \(t,-\overline t\) and
\(\operatorname{Re}t>0\).

The proof composes the adjacent rank-one intertwiners exchanging the two
characters of each pair. It compares their effect on a base compact-finite
vector and the vector obtained by multiplying its compact restriction by
\(|k_{ii}|^2-|k_{ji}|^2\) for the rows of one pair. The relative multiplier is
\((1-2\operatorname{Re}t)/(1+2\operatorname{Re}t)\) by the rank-one integral
calculation. Schur's lemma compares the composed operator to the operator
from the given positive form. Each diagonal pairing with a conjugate test
vector is its scalar times a compact integral of a squared norm. Both test
vectors take value one at the identity, so positivity of the given form
forces the relative multiplier to be strictly positive. The denominator is
positive, giving \(\operatorname{Re}t<1/2\), and the other member of the pair
has the opposite real part. A fixed character has real part zero.

The argument follows the reflection of signature under induction in D. A.
Vogan Jr., *The unitary dual of GL(n) over an archimedean field* (1986),
Proposition 10.5, p. 476. Theorem 11.5(f)–(h), p. 479, describes adjacent
intertwiners for spherical parameters. For each selected pair in Lean, the
equal angular weights and common imaginary part give a common unitary
character twist of the spherical rank-one family, as in Definition 2.3 and
the paragraph following it, p. 452. In the notation of (2.2), pp. 451–452,
the complex character \(\delta_1(z)=|z|^2\) gives the normalization above.
The Lean proof computes the two scalars directly using the Library's
normalized intertwining integral and uses irreducibility of the supplied
standard module in the signature comparison. The infinitesimal invariance
of the positive form is the condition in Knapp–Vogan, *Cohomological induction
and unitary representations* (1995), (0.5), p. 6.
