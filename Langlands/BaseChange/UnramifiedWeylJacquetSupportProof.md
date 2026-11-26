# Weyl Jacquet support of unramified principal series

`Langlands.BaseChange.unramifiedWeylJacquetSupport` proves
`Langlands.BaseChange.UnramifiedWeylJacquetSupportStatement.{uF,uV}`.
It uses the actual normalized upper Borel Jacquet module with the
published canonical uniformizer, integral diagonal fixed space and
spherical and generic predicates. The field and constituent carrier
universes are independent.

1. The associated-Levi geometric filtration gives a character line for
   each permutation. Exactness of integral diagonal generalized weights
   sums the line contributions to compute the Jacquet multiplicity of
   every tuple, including repeated Weyl weights.
2. Exactness of normalized Jacquet maps and of the weight functor on
   integral diagonal fixed vectors gives the submultiset bound for every
   irreducible admissible subquotient.
3. A spherical generic subquotient is a quotient of the series
   sorted by weakly increasing norms. The nondegeneracy of its nonzero
   subrepresentations and the one-dimensional top derivative show
   that the quotient map is an isomorphism. Its Borel Jacquet multiset is
   therefore the full Weyl multiset of the original tuple.
4. A weakly norm-decreasing weight gives an embedding into the series
   for that weight by a dual eigenfunctional and normalized first
   adjointness. Dualizing gives a quotient of a weakly norm-increasing
   series, whose spherical vector gives a spherical vector in the
   original irreducible representation by compact fixed-vector duality.

The geometric and order assertions are from Henniart–Lemaire,
*Changement de base et induction automorphe pour* \(GL_n\) *en
caractéristique non nulle*, Mém. Soc. Math. Fr. 124 (2011), I.5.4,
printed pp. 33–35, and I.5.5, Lemme 1, printed pp. 35–36
(PDF pp. 41–44). The uniformizer norm convention reverses the order on
real exponents used there. The registered source is
`provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61`
with SHA-256
`7af2940c75a75937c1bf9096eb329931d4245cf592e3572db0ff93ec6e76c5e0`.
[Henniart–Lemaire on Numdam](https://www.numdam.org/item/MSMF_2011_2_124__1_0/)
