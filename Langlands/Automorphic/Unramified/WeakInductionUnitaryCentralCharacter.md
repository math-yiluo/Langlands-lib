# Unitary central characters of cuspidal weak inductions

`WeakInductionUnitaryCentralCharacterStatement` concerns a number-field extension `E/F`
and actual cuspidal realizations `T` over `E` and `S` over `F` of positive ranks.
If `T` has unitary central character and `S.isoClass.IsWeakInductionOf T.isoClass`,
then `S` has unitary central character. The two field universes and the two presentation
universes are independent.

The proof chooses the central character `ω` of `S` by irreducibility and takes
genuine spectral presentations of `S` and `T` from the weak-induction hypothesis.
For a place outside the exceptional set of a presentation, the absolute value of
the leading coefficient of its Euler denominator is the absolute value of its
central character at the canonical uniformizer. The degree is the positive
representation rank. The leading coefficient is the top elementary symmetric
function of the Satake parameters times the sign given by that rank.
`finiteUniformizerValue_eq_elementaryCoefficient` identifies the top elementary
symmetric function with the central character value.

At each place where the weak-induction identity holds, the downstairs Euler
denominator is the product of the upstairs denominators after the substitutions
`X ↦ X^f`, with `f` the positive residue degree of the corresponding place.
Each substitution preserves the leading coefficient because the substituted
monomial is monic of positive degree. The product therefore has leading coefficient
of absolute value one by the unitarity of the upstairs central character.
At almost every downstairs place, `ω` is unramified and its uniformizer value has
absolute value one. The Hecke character obtained by applying the continuous complex
modulus character to `ω` is then trivial on the integral units and a uniformizer
at each such place, so its full local component is trivial.
`heckeLocalComponentRigidity` makes this modulus character globally trivial.

This is a consequence of the weak Euler-product comparison described for cyclic
extensions in Henniart (2012), *Induction automorphe globale pour les corps de nombres*,
§1.1, printed p. 2 (PDF p. 3). The proof only uses the Euler identity on the
given realizations, so it applies to every number-field extension with that identity.
