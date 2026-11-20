# Twisted conjugation across a vector quotient

`vectorQuotientHomeomorph` identifies the actual left quotient with the
additive coordinate space of a continuous open surjective homomorphism
whose kernel is the indicated subgroup. The quotient action is additive
translation, so the transported regular compatible measure is a scalar
multiple of additive Haar measure.

If the group automorphism acts on the quotient by \(A\), the quotient
displacement is \(1-A\). When this map is a linear equivalence, the Library's
matrix change of variables gives the inverse of the absolute determinant
as the pushforward factor. `map_twistedConjugationMap_of_vectorQuotient`
multiplies it by the factor on the kernel via the normal-subgroup Haar
identity. This is an internal step for calculating Iwasawa normalization
with the actual compact subgroup in Waldspurger's Lemma V.3.1.
