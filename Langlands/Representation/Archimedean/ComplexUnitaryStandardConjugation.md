# Conjugation of complex principal series

Conjugating the value of a character of weight `m` and exponent `t` changes the
parameters to `-m` and `conj t`. Taking its inverse then gives the Hermitian
contragredient parameters `m` and `-conj t`. This involution fixes exactly the
parameters whose exponent has real part zero.

The principal series uses the character normalization in the Library's
`ComplexCharacterData`, corresponding to Knapp, *Local Langlands Correspondence:
The Archimedean Case* (1994), §4, equation (4.2) on p. 405. Pointwise conjugation
preserves smoothness and maps the finite span of right translates semilinearly
onto the span of the conjugated translates. The real modulus factor commutes
with conjugation. The two equivariance laws follow from the formulas for right
translation and differentiation. This is the compact-finite conjugation used in
the Hermitian duality of Vogan, *The Unitary Dual of GL(n) over an Archimedean
Field* (1986), §10, Proposition 10.5, pp. 475–476.
