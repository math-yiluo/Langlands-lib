# Conductor bounds for norm pullback and products with a finite family

`DeepNormTwistConductorsStatement` fixes finite abelian Galois p-adic
field data, a residue degree, a different exponent, the set of norm-trivial
characters and a finite family of continuous lower quasicharacters.
For any two conductor bounds, there is a lower depth `N` such that a
continuous lower character of conductor strictly greater than `N`
satisfies both bounds after twisting. Its products with the finite family
and their inverses meet the first bound. Its upper norm pullback and its
inverse meet the second.

Choose `N` at least the first bound and at least the conductors of every
character in the finite family. A lower character of conductor greater
than `N` is nontrivial on the principal units at level `N`, where every
member of the finite family is trivial. The products therefore have
conductor greater than `N` as well. Inversion preserves the unit levels
on which a character is trivial and hence its conductor.

The rank-one norm conductor formula bounds the original lower conductor
by the residue degree times the sum of the upper conductor and the different
exponent. The inequality uses the term indexed by the trivial norm character.
Taking `N` also at least the residue degree times the sum of the second
bound and the different exponent forces the norm-pullback conductor to meet
the prescribed second bound.

The norm conductor step uses the Library's exponent calculation from
Arthur–Clozel, Chapter 1, equation (6.7), printed p. 60 (PDF p. 74), literature
ID `arthur-clozel-1989-base-change`, SHA-256
`c2e47ee562810367ebcacd3f1c242eda40b9e78b271668e36d99ce31001f9a19`.
