# Reduction of cyclic regular orbit lifting

`Langlands.Automorphic.Unramified.cyclicRegularOrbitLiftReduction` proves
`CyclicRegularOrbitLiftReductionStatement.{uF,uE,uV,uW}`. It takes the actual
regular-induction existence, weak induction to full-orbit weak base change,
and cyclic constituent-pair multiplicity propositions as premises.

For a regular upper cusp, the orbit map is injective. If two automorphisms
give the same conjugate, their quotient fixes the cusp. Write that quotient
as a power of the supplied generator with exponent less than the extension
degree. Regularity forces the exponent to be zero. Arithmetic pullback carries
the unitary central character to each conjugate, so every orbit constituent
is unitarizable. The resulting orbit has exactly `[E:F]` equal pairs with itself.

The existence premise supplies an actual lower cusp of the multiplied rank
with unitary central character. The comparison premise supplies weak base
change from its singleton to the upper orbit with the published spectral
attachments. The pair formula applied to this singleton with itself yields
one contribution per norm-character power, since their sum equals the
extension degree and each summand is at most one. In degree greater than one
this includes fixation by the supplied character. In degree one the character
is trivial by the norm-triviality exponent identity.

With a unitary competitor as the second lower datum, each summand is the
multiplicity of the witness in that competitor. Cancelling the positive
extension degree gives multiplicity one. The rank equality in the two weak
base-change relations and positivity of all constituent ranks make the
competitor the singleton. Equality with the singleton gives the converse by
the same comparison premise.

The argument formalizes the pair-count step of Arthur and Clozel,
*Simple Algebras, Base Change, and the Advanced Theory of the Trace Formula*
(1989), Chapter III, Lemma 6.4, printed pp. 217–218. Its pair formula uses
III.3.1, p. 201, and III.4.3, p. 204. The regular-orbit branch of Harris,
*The local Langlands conjecture for GL(n) over a p-adic field, n < p* (1998),
Proposition 4.8, printed pp. 202–203, invokes Lemma III.6.4.
