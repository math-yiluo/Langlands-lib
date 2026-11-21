# Finiteness of the rational Weyl group of GLₙ

For every field `F` and rank `n`, `WeylTorus.finite_rationalWeylGroup` proves that
`WeylTorus.RationalWeylGroup T` is finite. The positivity of its natural cardinal
follows because the quotient is nonempty. The second lemma supplies positivity
for the cardinal appearing in the Weyl integration weight of Henniart–Lemaire
(2011), II.2.10, printed p. 71.

Choose a regular semisimple `γ` whose centralizer is `T`. Conjugation sends `γ`
by any element of the normalizer to an element of `T` with the same characteristic
polynomial. If two conjugates agree, the quotient of the two normalizer
representatives centralizes `γ`, so they belong to the same coset modulo `T`.

To bound the possible conjugates, extend coefficients to an algebraic closure.
The characteristic polynomial of `γ` has distinct roots there. Enumerate them
and use squarefree characteristic-polynomial conjugacy to diagonalize `γ`.
Every matrix commuting with this diagonal matrix is diagonal in the same basis,
by comparing its off-diagonal entries in the commutation relation. The diagonal
entries of any matrix in the characteristic-polynomial fiber are roots of
that same polynomial. Thus the possible conjugates inject into the finite
type of tuples of its roots. This argument also covers the empty tuple in rank
zero.
