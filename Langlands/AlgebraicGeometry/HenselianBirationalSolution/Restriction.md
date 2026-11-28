# Restricting the law to an open subscheme

`exists_strictRestriction` constructs a `BirationalGroupLaw` on the given open
subscheme `Y`. Its domain consists of the pairs in the original domain whose two
inputs and product lie in `Y`. The two universal translations are restrictions of
the original open immersions. Associativity follows from the original law by
composing with the monomorphism `Y ⟶ X`.

The strictness witness supplies subsets of the domain and the two translation
images. For a point in `Y ×_S Y`, a generization in any of these subsets over a
fixed projection coordinate lifts back to `Y ×_S Y`, since the inclusion is open.
This gives all six densities of `IsStrictDomain`. The same open inclusion gives a
factorization for any scheme-valued product whose two inputs and output lie in `Y`.

This is the restriction of a representative used in Bosch, Lütkebohmert and
Raynaud, *Néron Models* (1990), §5.2 Proposition 2, pp. 115–117, with strictness
supplied by `IsStrictOn`.
