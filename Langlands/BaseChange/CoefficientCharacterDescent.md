# A regular character times a conjugate coefficient on the central quotient

In the nontrivial-central-character form of Clozel's formula (3.1), the character
and the test function transform by inverse central characters. For a conjugate
coefficient, the inverse occurs because the central character is unitary.
`characterCoefficientProduct` constructs their product on `GL_n(F) / Z`.

Multiplication by a central element preserves regular semisimplicity by the
scalar-multiplication lemma for `GL_n`. The extension `regularCharacterExtension`
uses the given character values on the regular semisimple locus and is zero
elsewhere. On the regular locus the local character translation law, followed by
uniqueness of the local value, multiplies the character by the scalar `χ(z)`.
The conjugate coefficient is multiplied by `star (χ(z))`. Their product is
unchanged because these two scalars have product `1`. The quotient lift gives
`characterCoefficientProduct_mk` at every representative.

`IsCharacterFunction.regularCharacterExtension` shows that taking the zero
extension preserves the distribution identity when the given function represents
the character. It uses Haar conullity of the regular semisimple locus and
invariance of the density identity under almost-everywhere equality.

**Source.** Laurent Clozel, *Invariant harmonic analysis on the Schwartz space of a
reductive p-adic group*, in Barker and Sally (eds.), *Harmonic Analysis on Reductive
Groups*, Progress in Mathematics 101, Birkhäuser, 1991, §3, formula (3.1)
and its extension to nontrivial central character, printed pp. 110–111
(PDF pp. 121–122). Literature ID
`provided-698170812a35ff43dbc4156af9f67a8384f95d97d5836529575e646643af617b`.
SHA-256 `c5cb36139e9cf3ed29fe1338a45488236cc69abdc4806d5ba2180456faba08ba`.
