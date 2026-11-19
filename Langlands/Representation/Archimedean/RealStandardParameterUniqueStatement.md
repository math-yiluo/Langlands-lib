# Uniqueness of the positive-weight real standard parameters

`Langlands.Archimedean.RealPositiveWeightStandardUniqueStatement` concerns
the actual `O(n)`-finite standard modules of two real block lists of rank `n`.
Both modules are irreducible under the Library's `realStandardRep` and
`realStandardLie` actions. Each induced block in either list has strictly
positive weight. A bijective `IsRealStandardIntertwiner` then implies that the
lists are permutations of each other.

The positive-weight convention is Knapp's convention for the irreducible real
Weil induction in formula (3.3) of *Local Langlands Correspondence: The
Archimedean Case* (`knapp-1994-archimedean-llc`, p. 402). It chooses one
representative of each opposite-weight pair and excludes the reducible
induction of weight zero. The corresponding real standard building blocks are
the characters and twisted discrete series in (2.2), p. 400.

The statement is derived from the uniqueness in Knapp's Theorem 1(c), p. 400.
That theorem concerns Langlands quotients of ordered data. The version here
concerns irreducible standard modules presented in arbitrary order. Applying
the source theorem to this version requires relating each irreducible standard
module to the Langlands quotient of its ordered data. The statement includes
rank zero, where both lists have to be empty. This module records the
proposition.
