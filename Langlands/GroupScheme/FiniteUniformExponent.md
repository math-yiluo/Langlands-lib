# Finite group schemes over a field have a uniform positive exponent

Authors: Workers 1575 and 16.

`Langlands.GroupScheme.finiteGroupSchemeUniformExponent` proves exactly the
published `Langlands.GroupScheme.FiniteGroupSchemeUniformExponentStatement`.
For every field k and every group scheme G over Spec k whose structure map
is finite, there exists one positive natural number n such that x^n = 1
for every point of G on every scheme over Spec k. The theorem has one
universe parameter, as does the target. There is no commutativity, smoothness,
perfectness, reducedness, or characteristic hypothesis on G or k.

The source statement is the existence consequence of J. S. Milne,
*Algebraic Groups* (2017), Proposition 11.32, printed page 221
(PDF page 237), registered as `milne-2017-algebraic-groups`. The original
source is `/home/taskhub/central-library/Milne--Algebraic groups, the theory of group schemes of finite type over a field (book)--2017.pdf`,
SHA-256 `899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
The relevant original pages and complete retained official errata snapshot
were read; the errata do not change the cited proposition. Milne gives the
stronger exponent equal to the group-scheme order. The implemented proof
establishes the requested existence of a positive exponent, without a bound.

The implemented algebraic argument is described in
`Langlands/Algebra/FiniteHopfUniformExponent.md`. Finiteness of residue-field
algebra maps supplies a common positive convolution exponent modulo the
nilradical of the finite coordinate algebra. In positive characteristic,
nilpotence of the nilradical and the prime-power binomial identity kill the
remaining difference in the convolution ring of linear maps. In characteristic
zero, `Langlands.FiniteHopfCharZero.isReduced` gives reducedness using
translated tangent derivations and algebraic-closure descent, as described in
`Langlands/Algebra/FiniteHopfCharZero.md`. The coalgebra may be noncocommutative
throughout, so this applies to arbitrary finite group schemes.

This module transfers that algebraic result to the actual group scheme.
A finite structure map makes G affine. The published affine Hopf coordinate
isomorphism identifies G with the relative spectrum of its commutative
coordinate Hopf algebra. `finite_hopfAlgebra` obtains module finiteness from
the finite structure map using the affine criterion for finite morphisms.

`pow_eq_one_of_hopf_id` transfers an exponent of the coordinate-valued
universal point to all scheme-valued points. Under `Spec.mapMulEquiv`, the
identity algebra map is the identity scheme morphism of the relative
spectrum, regarded as a point of that group object. If its nth power is the
identity point, precomposing with any morphism from any test scheme proves
the same assertion for that point. The affine Hopf coordinate isomorphism
then transports the assertion to G. The geometric argument adapts the
published transfer in `CentralIsogeny.KernelTorsion`, using its identity-point
comparison without its commutativity argument.

The module also records the positive-characteristic and reduced-coordinate
specializations. The final theorem applies the unrestricted algebraic
exponent theorem and the universal-point transfer. All helper modules are
included with this candidate; the published target statement and its imports
are unchanged.
