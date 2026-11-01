# Signed Weyl reflection and exact Haar transport

This internal prerequisite uses the published signed long representative
`W = w * d`, where `d = diag((-1)^n, ..., -1, 1)`, and the actual
upper-unipotent group. It is derived from the published unsigned reflected
inverse transpose, alternating diagonal conjugation, and the positive Haar
modulus argument for involutive automorphisms.

`signedReflectedUnipotent` first conjugates by `d` and then applies the
unsigned reflection. Its actual group value is `W * iota(u) * W⁻¹`.
Alternating conjugation and unsigned reflection each negate the sum of
first-superdiagonal entries, so the composite preserves both the standard
character and its inverse for every supplied nontrivial additive character.
No conductor assumption enters the proof.

Alternating conjugation is an involutive continuous group automorphism.
The published involutive-automorphism theorem shows that it preserves every
regular Haar measure on the locally compact unipotent group. Composing with
the unsigned reflection gives exact signed Haar preservation. The product
version fixes the second variable and preserves every supplied S-finite
product measure under the stated S-finiteness assumptions.

The orbit integral theorem substitutes this signed automorphism into an
arbitrary complex-valued group function. It identifies the inverse-transpose
orbit with the ordinary orbit of the function left-translated by `W⁻¹`,
using the same inverse standard character and the same Haar measure. The
integrability equivalence uses the measurable embedding and its exact
pushforward identity; no regularity of the group function is assumed.
All results allow `n = 0`. These statements do not assert the gamma comparison.

The full product orbit transport and its integrability equivalence permit an
arbitrary measurable parameter type, parameter measure, family of group
functions and group arguments. They use the signed automorphism on the
unipotent coordinate and fix the parameter coordinate. The measures are
S-finite for this product transport.

`integral_signedInverseTransposeOrbit_left` proves standard left covariance
of the signed inverse-transpose orbit. After the exact orbit transport, it
uses right Haar invariance to substitute `u * p`; the inverse character
contributes the standard character at `p`. This total-integral identity
requires no unproved convergence premise and also holds for arbitrary group
functions under the displayed right-invariance assumption.
