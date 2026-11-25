# Conjugation and positivity for self-pair Whittaker integrals

Internal helper module for the proof of `CuspidalSelfPairContinuationStatement`.

Pointwise conjugation of an actual cuspidal realization is the Library construction
`CuspidalOperatorRealization.conjugate`. The cusp function of the conjugate vector is the
conjugate cusp function. Its Whittaker function for the inverse of a unitary additive
character is the conjugate Whittaker function: the proof moves conjugation through the
defining integral and uses `Unfolding.genericCharacter_inv`. The same conjugation preserves
the spherical conditions outside any given finite set.

A unitary central character multiplied by its conjugate is trivial. The possible pole set
for the trivial character is `{0,1}`, since the exponent of a power of the idele norm is
unique (`CuspidalPairPartialGammaGlobal.detPower_injective`). The Library's
`EqualAnalytic.equalAnalyticStatement_proof` therefore gives an unconditional holomorphic
continuation of the global self-pair integral to `Re s > 1`. The internal proposition
`UnitarySelfPairIntegralContinuationStatement` records exactly this consequence, and
`unitarySelfPairIntegralContinuation` proves it. Its hypotheses quantify over an actual
cuspidal realization, its supplied unitary central character, a standard additive
character, an actual vector and a Schwartz–Bruhat test function. Its conclusion is a
holomorphic function on that half-plane agreeing with the global integral sufficiently
far to the right. It makes no assertion about the partial Euler product.

The final helper retains `EqualUnfoldingStatement` as an explicit premise to identify that
continuation with the Whittaker integral on a right half-plane. This module does not prove
that premise; the Library proves it as `equalUnfoldingStatement_proof` (module
`EqualUnfoldingProof`). This module is not a proof of `CuspidalSelfPairContinuationStatement`.

For a real-valued test function, the self-pair Whittaker integrand is exactly
`norm(W(g))^2 * Phi(e_n g) * exp(s * log(abs(det(g))))`. At a real parameter this is a real
quantity, nonnegative when `Phi` is nonnegative. These identities require neither
integrability nor unfolding.

The integral conventions and analytic input are those of Cogdell (2004), section 2.3,
printed pages 208–211 and Theorem 2.2, as already documented by the imported Library
modules. The identities here are derived directly from those Library definitions.
They are intended for a positivity variant of the argument for Jacquet–Shalika (1981) I,
Lemma (5.2), printed pages 554–555; the positivity variant is internal work, rather than a
claim that Jacquet–Shalika implement this route.
