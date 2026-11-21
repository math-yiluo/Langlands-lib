# Simultaneous descent for the prescribed adelic tensor factors

The finite adelic translation algebra acts in the grouped finite slot. The
compact and Lie generators in each infinite slot satisfy Jacobson density
when the corresponding local module is irreducible, admissible, compact-finite
and has continuous compact coefficients. The proof transports this density
along `ULift.moduleEquiv` by conjugation and applies the finite tensor density
criterion to the common free operator action.

`HasPlaceEmbeddings` asks for an injective intertwiner of the grouped finite
adelic factor and injective compact and Lie intertwiners of the individual
real and complex factors into one irreducible automorphic quotient.
`exists_with_placeEmbeddings` starts with an irreducible tensor presented as
a quotient of a stable space of genuine automorphic forms for the common
free operators. It applies `exists_irreducibleOperatorSubquotient_with_slotEmbeddings`,
then identifies the free generators with the actual place actions on the
quotient. For each archimedean factor, precomposing its injection with the
inverse of `ULift.moduleEquiv` gives the required injection of its original
carrier and preserves both intertwining identities.

This is the algebraic tensor step of Langlands (1979), Lemma 1, printed p. 203
(Corvallis I PDF p. 198), and the quotient step in the proof of Proposition 2,
printed pp. 205–206 (PDF pp. 200–201), in the application to Getz–Hahn
(2024), Theorem 10.7.5, printed p. 288 (PDF p. 300).
