# Transitivity of normalized enveloping center projections

For algebra maps \(A \to B \to C\), a `RelativeEnvelopingDecomposition`
characterizes projection of a central element by its unique representative
modulo a specified right ideal. `centerProjection_comp` proves transitivity
when the outer ideal and the image of the inner ideal lie in the ideal of
the direct projection. It writes the difference between the original
element and its two-step representative as the sum of the two remainders.
Uniqueness in the direct decomposition identifies the projections.

An automorphism of \(B\) that restricts to an automorphism of \(A\) and
preserves the inner ideal commutes with the inner projection. The proof
applies the automorphism to the congruence and uses uniqueness again.
`NormalizedCenterProjectionTransitivityStatement` applies this identity
with the outer shift on \(B\), followed on \(A\) by the inner shift.
The direct normalization is their composition on \(A\).
`sub_normalizedCenterProjection_mem` recovers the original congruence
by applying the inverse shift to the normalized value.

This is a right-ideal version of the algebra in Knapp and Vogan,
*Cohomological Induction and Unitary Representations* (1995), Chapter IV
§8, Lemma 4.123 and Proposition 4.129(a)–(b), pp. 301–303. Passing
through the enveloping antipode converts the source's congruence for
central elements to the right-ideal convention. In that convention,
the normalization shifts a Levi generator by \(+\rho\). It inverts the
shift by \(-\rho\) from differentiating the inverse half-modulus in the
restriction of a function. For a nested Cartan,
Levi and ambient Lie algebra, the ideal inclusions come from containment
of the nilradical directions. A character shift for the ambient
parabolic restricts to the Cartan shift and preserves the inner
nilradical ideal when its character vanishes on the inner nilradical.
The direct shift then restricts on the Cartan to the sum of the two
character shifts, as in (4.125). The Lean result uses the ideal
inclusions and shift identities as hypotheses on arbitrary associative
algebras over a commutative ring.
