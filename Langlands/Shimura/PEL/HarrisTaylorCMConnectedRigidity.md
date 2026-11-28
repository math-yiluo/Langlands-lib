# Uniqueness of normalized CM witnesses on connected bases

The rational Hom lemmas assume
`ConnectedGeometricPointHomFaithfulnessStatement`. For
`rationalHom_eq_zero_of_geometricBaseChange`, clear the denominator of a
rational homomorphism whose pullback to an algebraically closed point is
zero. A further nonzero integer multiple of the resulting integral
homomorphism pulls back to zero integrally. Apply the geometric-point
faithfulness hypothesis to that multiple, use torsion freeness of integral
Hom with invertible integers, then divide by the original denominator in
rational Hom. `rationalBaseChangeHom_injective_of_geometricPoint` uses
this result on the difference of two morphisms and the composition
comparison for a base map followed by a point of its source.

`witness_eq_of_geometricRigidity` assumes geometric coarse-level
rigidity at the given Harris level. Its representatives over the
connected locally noetherian test are taken at the geometric point
expressed as \(\operatorname{id}\) followed by \(z\). The first
representative satisfies the positive object and numerical conditions.
Compose the first witness with the inverse of the second to obtain an
automorphism respecting the first orbit and multiplying its polarization
by the quotient of the multipliers. Pull this witness back to
\(\operatorname{Spec}\Omega\) along \(z\), where the theorem applies
geometric rigidity to its action isomorphism. Rational Hom detection
then gives the identity over the test, so cancellation shows that the
original action isomorphisms agree.

The one-point integral faithfulness assumption is the abelian-scheme
specialization of the rigidity lemma in Mumford, Fogarty and Kirwan,
*Geometric Invariant Theory*, third enlarged edition (1994), Chapter 6,
§1, Proposition 6.1 and Corollary 6.2, pp. 115–116.
